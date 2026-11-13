import { describe, expect, it } from "vitest";
import { provePcodeControlFlow } from "./provenPcodeControlFlow.js";
import { availableNativeValueFlowSchema } from "./nativeValueFlow.js";

const constant = (value: number, bytes = 8) => ({
  kind: "constant",
  location: null,
  size_bytes: bytes,
  constant_hex: value.toString(16),
});
const temporary = (name: string, bytes = 8) => ({
  kind: "unique",
  location: `unique:0x${name}`,
  size_bytes: bytes,
  constant_hex: null,
});
const operation = (
  id: string,
  opcode: string,
  inputs: unknown[],
  output: unknown = null,
  address = "0x1000",
) => ({
  id,
  address,
  sequence: Number(id.slice(1)) || 0,
  opcode,
  is_dead: false,
  block_membership: "member",
  inputs,
  output,
});
const flow = (
  operations: unknown[],
  def_use: { definition: string; use: string; input_index: number }[] = [],
  truncated = false,
) =>
  availableNativeValueFlowSchema.parse({
    available: true,
    provenance: "ghidra-high-pcode",
    operations,
    def_use,
    effects: [],
    parameters: [],
    parameter_uses: [],
    truncated,
    omitted_operations_lower_bound: 0,
    known_omitted_inputs: truncated ? 1 : 0,
    known_omitted_edges: 0,
    limitations: ["High p-code only"],
  });

describe("bounded high-p-code control flow", () => {
  it("proves x XOR x == 0 across a valid SSA source and a taken opaque predicate", () => {
    const x = temporary("10");
    const y = temporary("20");
    const p = temporary("30", 1);
    const operations = [
      operation("p1", "LOAD", [constant(0), constant(0x100)], x),
      operation("p2", "INT_XOR", [x, x], y),
      operation("p3", "INT_EQUAL", [y, constant(0)], p),
      operation("p4", "CBRANCH", [constant(0x1020), p]),
    ];
    const edges = [
      { definition: "p1", use: "p2", input_index: 0 },
      { definition: "p1", use: "p2", input_index: 1 },
      { definition: "p2", use: "p3", input_index: 0 },
      { definition: "p3", use: "p4", input_index: 1 },
    ];
    const source = flow(operations, edges);
    const proof = provePcodeControlFlow(source);
    expect(proof.proven_conditions).toEqual([
      {
        operation: "p4",
        address: "0x1000",
        outcome: "taken",
        proof: "exact",
        constant_hex: "1",
      },
    ]);
    expect(proof.unknown_conditional_branches).toBe(0);
    expect(source.operations).toEqual(operations);
  });

  it("retains both edges when a branch uses unknown memory", () => {
    const x = temporary("10", 1);
    const proof = provePcodeControlFlow(
      flow(
        [
          operation("p1", "LOAD", [constant(0), constant(0x123)], x),
          operation("p2", "CBRANCH", [constant(0x1020), x]),
        ],
        [{ definition: "p1", use: "p2", input_index: 1 }],
      ),
    );
    expect(proof.proven_conditions).toEqual([]);
    expect(proof.unknown_conditional_branches).toBe(1);
  });

  it("proves fallthrough only for zero and rejects missing SSA links", () => {
    const p = temporary("01", 1);
    const result = provePcodeControlFlow(
      flow(
        [
          operation("p1", "COPY", [constant(0, 1)], p),
          operation("p2", "CBRANCH", [constant(0x1020), p]),
          operation("p3", "CBRANCH", [constant(0x1020), temporary("03", 1)]),
        ],
        [{ definition: "p1", use: "p2", input_index: 1 }],
      ),
    );
    expect(result.proven_conditions.map(({ outcome }) => outcome)).toEqual([
      "fallthrough",
    ]);
    expect(result.unknown_conditional_branches).toBe(1);
  });

  it("resolves a constant indirect target only when it belongs to the same HighFunction and address space", () => {
    const target = temporary("40");
    const observed = [
      operation("p1", "INT_ADD", [constant(0x1000), constant(0x20)], target),
      operation("p2", "BRANCHIND", [target]),
      operation("p3", "COPY", [constant(1)], temporary("50"), "0x1020"),
      operation("p4", "BRANCHIND", [constant(0x2000)]),
    ];
    const results = provePcodeControlFlow(
      flow(observed, [{ definition: "p1", use: "p2", input_index: 0 }]),
    );
    expect(results.resolved_indirect_targets).toEqual([
      {
        operation: "p2",
        address: "0x1000",
        target_address: "0x1020",
      },
    ]);
    expect(results.unknown_indirect_branches).toBe(1);
  });

  it("does not conflate address spaces when resolving indirect branches", () => {
    const results = provePcodeControlFlow(
      flow([
        operation("p1", "BRANCHIND", [constant(0x2000)], null, "ram:0x1000"),
        operation("p2", "COPY", [constant(1)], temporary("20"), "rom:0x2000"),
      ]),
    );
    expect(results.resolved_indirect_targets).toEqual([]);
    expect(results.unknown_indirect_branches).toBe(1);
  });

  it("refuses truncated PHI inputs and recursion cycles", () => {
    const a = temporary("10", 1);
    const b = temporary("20", 1);
    const phi = flow(
      [
        operation("p1", "MULTIEQUAL", [constant(1, 1), constant(1, 1)], a),
        operation("p2", "CBRANCH", [constant(0x1020), a]),
      ],
      [{ definition: "p1", use: "p2", input_index: 1 }],
      true,
    );
    expect(provePcodeControlFlow(phi).proven_conditions).toEqual([]);
    const cycle = flow(
      [
        operation("p1", "COPY", [b], a),
        operation("p2", "COPY", [a], b),
        operation("p3", "CBRANCH", [constant(0x2000), a]),
      ],
      [
        { definition: "p2", use: "p1", input_index: 0 },
        { definition: "p1", use: "p2", input_index: 0 },
        { definition: "p1", use: "p3", input_index: 1 },
      ],
    );
    expect(provePcodeControlFlow(cycle).unknown_conditional_branches).toBe(1);
  });

  it("checks variable-width arithmetic with signed extension", () => {
    const x = temporary("11", 8);
    const decision = temporary("12", 1);
    const result = provePcodeControlFlow(
      flow(
        [
          operation("p1", "INT_SEXT", [constant(0xff, 1)], x),
          operation("p2", "INT_SLESS", [x, constant(0, 8)], decision),
          operation("p3", "CBRANCH", [constant(0x3000), decision]),
        ],
        [
          { definition: "p1", use: "p2", input_index: 0 },
          { definition: "p2", use: "p3", input_index: 1 },
        ],
      ),
    );
    expect(result.proven_conditions).toEqual([
      {
        operation: "p3",
        address: "0x1000",
        outcome: "taken",
        proof: "exact",
        constant_hex: "1",
      },
    ]);
  });
});

it("proves bitmask-disjoint opaque equality false without knowing x", () => {
  const x = temporary("10");
  const masked = temporary("11");
  const decision = temporary("12", 1);
  const result = provePcodeControlFlow(
    flow(
      [
        operation("p1", "LOAD", [constant(0), constant(0x100)], x),
        operation("p2", "INT_AND", [x, constant(1)], masked),
        operation("p3", "INT_EQUAL", [masked, constant(2)], decision),
        operation("p4", "CBRANCH", [constant(0x1020), decision]),
      ],
      [
        { definition: "p1", use: "p2", input_index: 0 },
        { definition: "p2", use: "p3", input_index: 0 },
        { definition: "p3", use: "p4", input_index: 1 },
      ],
    ),
  );
  expect(result.proven_conditions).toEqual([
    {
      operation: "p4",
      address: "0x1000",
      outcome: "fallthrough",
      proof: "known-bits",
      constant_hex: null,
    },
  ]);
});

it("proves that x OR 1 cannot be zero without reading x", () => {
  const x = temporary("10");
  const resultNode = temporary("20");
  const result = provePcodeControlFlow(
    flow(
      [
        operation("p1", "LOAD", [constant(0), constant(0x100)], x),
        operation("p2", "INT_OR", [x, constant(1)], resultNode),
        operation("p3", "CBRANCH", [constant(0x1020), resultNode]),
      ],
      [
        { definition: "p1", use: "p2", input_index: 0 },
        { definition: "p2", use: "p3", input_index: 1 },
      ],
    ),
  );
  expect(result.proven_conditions).toEqual([
    {
      operation: "p3",
      address: "0x1000",
      outcome: "taken",
      proof: "known-bits",
      constant_hex: null,
    },
  ]);
});

it("does not prove branches from contradictory SSA identities or operand widths", () => {
  const same = temporary("10");
  const alien = temporary("20");
  const xor = temporary("30");
  const result = provePcodeControlFlow(
    flow(
      [
        operation("p1", "LOAD", [constant(0), constant(0x100)], same),
        operation("p2", "INT_XOR", [same, alien], xor),
        operation("p3", "CBRANCH", [constant(0x1100), xor]),
        operation(
          "p4",
          "INT_EQUAL",
          [constant(1, 8), constant(1, 1)],
          temporary("50", 1),
        ),
        operation("p5", "CBRANCH", [constant(0x1100), temporary("50", 1)]),
      ],
      [
        { definition: "p1", use: "p2", input_index: 0 },
        { definition: "p1", use: "p2", input_index: 1 },
        { definition: "p2", use: "p3", input_index: 1 },
        { definition: "p4", use: "p5", input_index: 1 },
      ],
    ),
  );
  expect(result.proven_conditions).toEqual([]);
  expect(result.unknown_conditional_branches).toBe(2);
});
