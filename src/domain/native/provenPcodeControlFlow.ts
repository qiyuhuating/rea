import type { z } from "zod";
import { addressCoordinate } from "./addressCoordinate.js";
import type { availableNativeValueFlowSchema } from "./nativeValueFlow.js";

type Flow = z.infer<typeof availableNativeValueFlowSchema>;
type Operation = Flow["operations"][number];
type Varnode = Operation["inputs"][number];

const MAX_PROOF_STEPS = 4_096;
const MAX_PROOF_DEPTH = 32;
const mask = (bytes: number): bigint => (1n << BigInt(bytes * 8)) - 1n;
const validWidth = (bytes: number): boolean => bytes >= 1 && bytes <= 8;
const signed = (value: bigint, bytes: number): bigint => {
  const bits = BigInt(bytes * 8);
  const sign = 1n << (bits - 1n);
  return (value & sign) === 0n ? value : value - (1n << bits);
};

/**
 * Conservatively prove high-p-code branches with bounded SSA bitvector evaluation.
 * Missing definitions, calls, loads, recursion and unsupported opcodes stay unknown.
 * The original provider CFG and pseudocode are never modified.
 */
export const provePcodeControlFlow = (flow: Flow) => {
  const operations = new Map(flow.operations.map((op) => [op.id, op]));
  const definitions = new Map<string, string | null>();
  for (const edge of flow.def_use) {
    const key = `${edge.use}:${edge.input_index}`;
    definitions.set(key, definitions.has(key) ? null : edge.definition);
  }

  const memo = new Map<string, bigint | null>();
  const active = new Set<string>();
  let steps = 0;
  let budgetExhausted = false;

  const constant = (node: Varnode | undefined): bigint | null => {
    if (
      node?.kind !== "constant" ||
      node.constant_hex === null ||
      node.constant_hex.length > 16 ||
      !validWidth(node.size_bytes)
    )
      return null;
    return BigInt(`0x${node.constant_hex}`) & mask(node.size_bytes);
  };

  const sameSource = (op: Operation, left: number, right: number): boolean => {
    const a = op.inputs[left],
      b = op.inputs[right];
    if (!a || !b || a.size_bytes !== b.size_bytes) return false;
    const ac = constant(a),
      bc = constant(b);
    if (ac !== null && bc !== null) return ac === bc;
    const ad = definitions.get(`${op.id}:${left}`);
    const bd = definitions.get(`${op.id}:${right}`);
    const source =
      ad === undefined || ad === null ? null : operations.get(ad)?.output;
    return (
      ad !== undefined &&
      ad !== null &&
      ad === bd &&
      a.kind === b.kind &&
      a.location === b.location &&
      source !== null &&
      source !== undefined &&
      source.kind === a.kind &&
      source.location === a.location &&
      source.size_bytes === a.size_bytes
    );
  };

  const evaluate = (id: string, depth: number): bigint | null => {
    if (memo.has(id)) return memo.get(id) ?? null;
    const op = operations.get(id);
    if (
      !op ||
      op.block_membership !== "member" ||
      !op.output ||
      !validWidth(op.output.size_bytes)
    )
      return null;
    if (active.has(id)) return null;
    if (steps >= MAX_PROOF_STEPS || depth >= MAX_PROOF_DEPTH) {
      budgetExhausted = true;
      return null;
    }
    steps++;
    active.add(id);
    const width = op.output.size_bytes;
    const bits = BigInt(width * 8);
    const modulus = mask(width);
    const input = (index: number): bigint | null => {
      const node = op.inputs[index];
      if (!node || !validWidth(node.size_bytes)) return null;
      const literal = constant(node);
      if (literal !== null) return literal;
      const sourceId = definitions.get(`${id}:${index}`);
      if (sourceId === undefined || sourceId === null) return null;
      const source = operations.get(sourceId)?.output;
      if (
        !source ||
        source.kind !== node.kind ||
        source.location !== node.location ||
        source.size_bytes !== node.size_bytes
      )
        return null;
      return evaluate(sourceId, depth + 1);
    };
    const a = input(0),
      b = input(1);
    const leftWidth = op.inputs[0]?.size_bytes;
    const rightWidth = op.inputs[1]?.size_bytes;
    const binaryWidth = leftWidth === width && rightWidth === width;
    const comparable =
      leftWidth !== undefined &&
      validWidth(leftWidth) &&
      leftWidth === rightWidth;
    let answer: bigint | null = null;
    switch (op.opcode) {
      case "COPY":
      case "CAST":
        if (a !== null && op.inputs[0]?.size_bytes === width) answer = a;
        break;
      case "INT_ZEXT":
        if (a !== null && leftWidth !== undefined && leftWidth <= width)
          answer = a;
        break;
      case "INT_SEXT":
        if (a !== null && leftWidth !== undefined && leftWidth <= width)
          answer = signed(a, leftWidth);
        break;
      case "INT_ADD":
        if (binaryWidth && a !== null && b !== null) answer = a + b;
        break;
      case "INT_SUB":
        if (!binaryWidth) break;
        if (sameSource(op, 0, 1)) answer = 0n;
        else if (a !== null && b !== null) answer = a - b;
        break;
      case "INT_MULT":
        if (!binaryWidth) break;
        if (a === 0n || b === 0n) answer = 0n;
        else if (a !== null && b !== null) answer = a * b;
        break;
      case "INT_AND":
        if (!binaryWidth) break;
        if (a === 0n || b === 0n) answer = 0n;
        else if (a !== null && b !== null) answer = a & b;
        break;
      case "INT_OR":
        if (!binaryWidth) break;
        if (a === modulus || b === modulus) answer = modulus;
        else if (a !== null && b !== null) answer = a | b;
        break;
      case "INT_XOR":
        if (!binaryWidth) break;
        if (sameSource(op, 0, 1)) answer = 0n;
        else if (a !== null && b !== null) answer = a ^ b;
        break;
      case "INT_NEGATE":
        if (leftWidth === width && a !== null) answer = ~a;
        break;
      case "INT_2COMP":
        if (leftWidth === width && a !== null) answer = -a;
        break;
      case "INT_EQUAL":
        if (!comparable) break;
        if (sameSource(op, 0, 1)) answer = 1n;
        else if (a !== null && b !== null) answer = a === b ? 1n : 0n;
        break;
      case "INT_NOTEQUAL":
        if (!comparable) break;
        if (sameSource(op, 0, 1)) answer = 0n;
        else if (a !== null && b !== null) answer = a !== b ? 1n : 0n;
        break;
      case "INT_LESS":
      case "INT_LESSEQUAL":
      case "INT_SLESS":
      case "INT_SLESSEQUAL":
        if (
          comparable &&
          a !== null &&
          b !== null &&
          op.inputs[0] &&
          op.inputs[1]
        ) {
          const x = op.opcode.startsWith("INT_S")
            ? signed(a, op.inputs[0].size_bytes)
            : a;
          const y = op.opcode.startsWith("INT_S")
            ? signed(b, op.inputs[1].size_bytes)
            : b;
          answer = (op.opcode.endsWith("LESSEQUAL") ? x <= y : x < y) ? 1n : 0n;
        }
        break;
      case "BOOL_NEGATE":
        if (a !== null) answer = a === 0n ? 1n : 0n;
        break;
      case "BOOL_AND":
        if (a === 0n || b === 0n) answer = 0n;
        else if (a !== null && b !== null) answer = 1n;
        break;
      case "BOOL_OR":
        if ((a !== null && a !== 0n) || (b !== null && b !== 0n)) answer = 1n;
        else if (a !== null && b !== null) answer = 0n;
        break;
      case "BOOL_XOR":
        if (sameSource(op, 0, 1)) answer = 0n;
        else if (a !== null && b !== null)
          answer = (a !== 0n) !== (b !== 0n) ? 1n : 0n;
        break;
      case "INT_LEFT":
      case "INT_RIGHT":
      case "INT_SRIGHT":
        if (leftWidth === width && a !== null && b !== null) {
          if (b >= bits)
            answer =
              op.opcode === "INT_SRIGHT" && signed(a, width) < 0n
                ? modulus
                : 0n;
          else if (op.opcode === "INT_LEFT") answer = a << b;
          else if (op.opcode === "INT_RIGHT") answer = a >> b;
          else answer = signed(a, width) >> b;
        }
        break;
      case "PIECE":
        if (
          a !== null &&
          b !== null &&
          leftWidth !== undefined &&
          rightWidth !== undefined &&
          leftWidth + rightWidth === width
        )
          answer = (a << BigInt(rightWidth * 8)) | b;
        break;
      case "SUBPIECE":
        if (
          a !== null &&
          b !== null &&
          leftWidth !== undefined &&
          b <= BigInt(leftWidth - width)
        )
          answer = a >> (b * 8n);
        break;
      case "MULTIEQUAL":
        if (
          !flow.truncated &&
          op.inputs.length > 0 &&
          op.inputs.every((node) => node.size_bytes === width)
        ) {
          const values = op.inputs.map((_, index) => input(index));
          if (
            values[0] !== null &&
            values.every((value) => value === values[0])
          )
            answer = values[0] ?? null;
        }
        break;
      default:
        break;
    }
    active.delete(id);
    const result = answer === null ? null : answer & modulus;
    memo.set(id, result);
    return result;
  };

  const inputValue = (op: Operation, index: number): bigint | null => {
    const node = op.inputs[index];
    const literal = constant(node);
    if (literal !== null) return literal;
    const definition = definitions.get(`${op.id}:${index}`);
    if (definition === undefined || definition === null || !node) return null;
    const output = operations.get(definition)?.output;
    if (
      !output ||
      output.kind !== node.kind ||
      output.location !== node.location ||
      output.size_bytes !== node.size_bytes
    )
      return null;
    return evaluate(definition, 0);
  };

  type Bits = { readonly zero: bigint; readonly one: bigint };
  const unknownBits: Bits = { zero: 0n, one: 0n };
  const bitMemo = new Map<string, Bits>();
  const bitActive = new Set<string>();
  const knownValue = (bits: Bits, bytes: number): bigint | null =>
    (bits.zero | bits.one) === mask(bytes) ? bits.one : null;
  const constantBits = (value: bigint, bytes: number): Bits => ({
    zero: ~value & mask(bytes),
    one: value & mask(bytes),
  });
  const bitsFor = (id: string, depth: number): Bits => {
    const remembered = bitMemo.get(id);
    if (remembered) return remembered;
    const op = operations.get(id);
    if (
      !op?.output ||
      !validWidth(op.output.size_bytes) ||
      op.block_membership !== "member" ||
      bitActive.has(id)
    )
      return unknownBits;
    if (steps >= MAX_PROOF_STEPS || depth >= MAX_PROOF_DEPTH) {
      budgetExhausted = true;
      return unknownBits;
    }
    steps++;
    bitActive.add(id);
    const bytes = op.output.size_bytes;
    const full = mask(bytes);
    const bitsInput = (index: number): Bits => {
      const node = op.inputs[index];
      if (!node || !validWidth(node.size_bytes)) return unknownBits;
      const value = constant(node);
      if (value !== null) return constantBits(value, node.size_bytes);
      const sourceId = definitions.get(`${id}:${index}`);
      if (sourceId === null || sourceId === undefined) return unknownBits;
      const source = operations.get(sourceId)?.output;
      if (
        !source ||
        source.kind !== node.kind ||
        source.location !== node.location ||
        source.size_bytes !== node.size_bytes
      )
        return unknownBits;
      return bitsFor(sourceId, depth + 1);
    };
    const a = bitsInput(0),
      b = bitsInput(1);
    const inputWidth = op.inputs[0]?.size_bytes;
    const binaryWidth =
      inputWidth === bytes && op.inputs[1]?.size_bytes === bytes;
    let result: Bits = unknownBits;
    switch (op.opcode) {
      case "COPY":
      case "CAST":
        if (inputWidth === bytes) result = a;
        break;
      case "INT_ZEXT":
        if (inputWidth !== undefined && inputWidth <= bytes)
          result = { zero: a.zero | (full ^ mask(inputWidth)), one: a.one };
        break;
      case "INT_AND":
        if (binaryWidth) result = { zero: a.zero | b.zero, one: a.one & b.one };
        break;
      case "INT_OR":
        if (binaryWidth) result = { zero: a.zero & b.zero, one: a.one | b.one };
        break;
      case "INT_XOR":
        if (binaryWidth)
          result = {
            zero: (a.zero & b.zero) | (a.one & b.one),
            one: (a.zero & b.one) | (a.one & b.zero),
          };
        break;
      case "INT_NEGATE":
        if (inputWidth === bytes) result = { zero: a.one, one: a.zero };
        break;
      case "INT_EQUAL":
      case "INT_NOTEQUAL": {
        const equal =
          sameSource(op, 0, 1) ||
          (inputWidth !== undefined &&
            validWidth(inputWidth) &&
            inputWidth === op.inputs[1]?.size_bytes &&
            knownValue(a, inputWidth) !== null &&
            knownValue(a, inputWidth) === knownValue(b, inputWidth));
        const unequal =
          inputWidth !== undefined &&
          validWidth(inputWidth) &&
          inputWidth === op.inputs[1]?.size_bytes &&
          ((a.one & b.zero) | (a.zero & b.one)) !== 0n;
        if (equal || unequal)
          result = constantBits(
            op.opcode === "INT_EQUAL" ? (equal ? 1n : 0n) : equal ? 0n : 1n,
            bytes,
          );
        break;
      }
      case "BOOL_NEGATE":
        if (inputWidth !== undefined && validWidth(inputWidth)) {
          const allZero = a.zero === mask(inputWidth);
          if (allZero || a.one !== 0n)
            result = constantBits(allZero ? 1n : 0n, bytes);
        }
        break;
      case "MULTIEQUAL":
        if (
          !flow.truncated &&
          op.inputs.length > 0 &&
          op.inputs.every((node) => node.size_bytes === bytes)
        ) {
          const all = op.inputs.map((_, index) => bitsInput(index));
          result = all.reduce((previous, next) => ({
            zero: previous.zero & next.zero,
            one: previous.one & next.one,
          }));
        }
        break;
      default:
        break;
    }
    result = { zero: result.zero & full, one: result.one & full };
    bitActive.delete(id);
    bitMemo.set(id, result);
    return result;
  };

  const inputBits = (op: Operation, index: number): Bits => {
    const node = op.inputs[index];
    if (!node || !validWidth(node.size_bytes)) return unknownBits;
    const literal = constant(node);
    if (literal !== null) return constantBits(literal, node.size_bytes);
    const sourceId = definitions.get(`${op.id}:${index}`);
    if (sourceId === null || sourceId === undefined) return unknownBits;
    const source = operations.get(sourceId)?.output;
    if (
      !source ||
      source.kind !== node.kind ||
      source.location !== node.location ||
      source.size_bytes !== node.size_bytes
    )
      return unknownBits;
    return bitsFor(sourceId, 0);
  };

  let knownAddresses: Map<string, string> | undefined;
  const targetAddress = (
    operation: Operation,
    offset: bigint,
  ): string | null => {
    const branch = addressCoordinate(operation.address);
    if (!branch) return null;
    if (!knownAddresses) {
      knownAddresses = new Map();
      for (const item of flow.operations) {
        const coordinate = addressCoordinate(item.address);
        if (coordinate)
          knownAddresses.set(
            `${coordinate.space ?? ""}:${coordinate.offset}`,
            item.address,
          );
      }
    }
    return knownAddresses.get(`${branch.space ?? ""}:${offset}`) ?? null;
  };

  const proven_conditions: {
    operation: string;
    address: string;
    outcome: "taken" | "fallthrough";
    proof: "exact" | "known-bits";
    constant_hex: string | null;
  }[] = [];
  const resolved_indirect_targets: {
    operation: string;
    address: string;
    target_address: string;
  }[] = [];
  let conditionalBranches = 0;
  let indirectBranches = 0;
  for (const operation of flow.operations) {
    if (operation.block_membership !== "member") continue;
    if (operation.opcode === "CBRANCH") {
      conditionalBranches++;
      const condition = inputValue(operation, 1);
      const width = operation.inputs[1]?.size_bytes;
      const bits = condition === null ? inputBits(operation, 1) : unknownBits;
      const outcome =
        condition !== null
          ? condition === 0n
            ? "fallthrough"
            : "taken"
          : width !== undefined &&
              validWidth(width) &&
              bits.zero === mask(width)
            ? "fallthrough"
            : bits.one !== 0n
              ? "taken"
              : null;
      if (outcome !== null)
        proven_conditions.push({
          operation: operation.id,
          address: operation.address,
          outcome,
          proof: condition === null ? "known-bits" : "exact",
          constant_hex: condition === null ? null : condition.toString(16),
        });
    } else if (operation.opcode === "BRANCHIND") {
      indirectBranches++;
      const target = inputValue(operation, 0);
      const address = target === null ? null : targetAddress(operation, target);
      if (address !== null)
        resolved_indirect_targets.push({
          operation: operation.id,
          address: operation.address,
          target_address: address,
        });
    }
  }
  return {
    analysis: "bounded-high-pcode-ssa-v1" as const,
    max_steps: MAX_PROOF_STEPS,
    evaluated_operations: steps,
    budget_exhausted: budgetExhausted,
    inspected_conditional_branches: conditionalBranches,
    inspected_indirect_branches: indirectBranches,
    proven_conditions,
    resolved_indirect_targets,
    unknown_conditional_branches:
      conditionalBranches - proven_conditions.length,
    unknown_indirect_branches:
      indirectBranches - resolved_indirect_targets.length,
    limitations: [
      "Proofs apply to Ghidra HighFunction p-code, not independently verified machine-code semantics. Original CFG edges and pseudocode are unchanged; unresolved paths remain unknown.",
      "Indirect targets require an exact instruction address match inside the same retained HighFunction and address space.",
    ],
  };
};
