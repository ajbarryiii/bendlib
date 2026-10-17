// Law-shape matcher: positive cases and planted negatives on statements exactly
// as bend 2.0.27's printer shows them (copied from bend-mathlib 0.1.0.1 and hub packages).

import { describe, expect, test } from "bun:test";
import { compile, looksLikeShape, matchStatement, parse, normalize, ShapeError } from "../src/shape.ts";

const LAWS: Record<string, [string, string]> = {
  append_nil: ["List.append(a, A, xs, [])", "xs"],
  nil_append: ["List.append(a, A, [], xs)", "xs"],
  append_assoc: ["List.append(a, A, List.append(a, A, xs, ys), zs)", "List.append(a, A, xs, List.append(a, A, ys, zs))"],
  add_zero: ["Nat.add(x, 0n)", "x"],
  zero_add: ["Nat.add(0n, x)", "x"],
  add_succ: ["Nat.add(n, 1n+m)", "1n+Nat.add(n, m)"],
  add_comm: ["Nat.add(n, m)", "Nat.add(m, n)"],
  mul_one: ["Nat.mul(x, 1n)", "x"],
  length_append: ["List.length(a, A, List.append(a, A, xs, ys))", "Nat.add(List.length(a, A, xs), List.length(a, A, ys))"],
  encode_row_empty: ["lib.Csv.encode_row([])", '""'],
  peek_empty: ["lib.Queue.peek(a, A, lib.Queue.empty(a, A))", "None{}"],
  cons_lit: ["List.append(Nat, 1n <> xs, [])", "[1n+x, 0n, 2n]"],
  reduce_numel: ["tinygrad/shape.numel(s)", "Nat.mul(tinygrad/shape.at(s, 0n), tinygrad/shape.numel(tinygrad/shape.drop_at(s, 0n)))"],
};

function hits(q: string): string[] {
  const p = compile(q);
  return Object.entries(LAWS).filter(([, [l, r]]) => matchStatement(p, l, r)).map(([k]) => k).sort();
}

describe("law-shape search", () => {
  test("List.append(_, Nil{}) finds exactly the right-identity shapes", () => {
    expect(hits("List.append(_, Nil{})")).toEqual(["append_nil", "cons_lit"]);
  });
  test("planted negative: nil_append has [] on the left, not the right", () => {
    expect(hits("List.append(_, Nil{})")).not.toContain("nil_append");
    expect(hits("List.append(Nil{}, _)")).toEqual(["nil_append"]);
  });
  test("Nat.add(_, 0n) finds add_zero but not zero_add", () => {
    expect(hits("Nat.add(_, 0n)")).toEqual(["add_zero"]);
    expect(hits("Nat.add(0n, _)")).toEqual(["zero_add"]);
  });
  test("Zero{} and Succ{…} in queries mean what the printer shows", () => {
    expect(hits("Nat.add(_, Zero{})")).toEqual(["add_zero"]);
    expect(hits("Nat.add(_, Succ{_})")).toEqual(["add_succ"]);
    expect(hits("Nat.mul(_, Succ{Zero{}})")).toEqual(["mul_one"]);
  });
  test("Con{h, t} is h <> t, and a Con chain ending in Nil is a list literal", () => {
    expect(hits("List.append(Con{_, _}, _)")).toEqual(["cons_lit"]);
    expect(hits("Con{_, Con{0n, Con{2n, Nil{}}}}")).toEqual(["cons_lit"]);
    expect(normalize(parse("Con{1n, Nil{}}"))).toEqual(parse("[1n]"));
  });
  test("a wildcard is one balanced sub-term: it spans a call but never a comma", () => {
    expect(hits("List.append(List.append(_, _), _)")).toEqual(["append_assoc"]);
    expect(hits("Nat.add(_)")).toEqual(["add_comm", "add_succ", "add_zero", "length_append", "zero_add"]);
    expect(hits("List.append(_)")).toEqual(["append_assoc", "append_nil", "cons_lit", "length_append", "nil_append"]);
  });
  test("an equation pattern must cover a whole side", () => {
    expect(hits("Nat.add(_, _) == Nat.add(_, _)")).toEqual(["add_comm"]);
    expect(hits("_ == 1n+_")).toEqual(["add_succ"]);
    expect(hits("Nat.add(n, _) == _")).toEqual(["add_comm", "add_succ"]);
  });
  test("leading type arguments may be omitted, trailing ones may not", () => {
    expect(hits("List.append(a, A, _, [])")).toEqual(["append_nil"]);
    expect(hits("List.append(xs)")).toEqual(["nil_append"]);
    expect(hits("List.append(acc)")).toEqual([]);
    expect(hits("List.append(_, _, _, _, _)")).toEqual([]);
  });
  test("names match on a namespace suffix, never on a partial segment", () => {
    expect(hits("Csv.encode_row([])")).toEqual(["encode_row_empty"]);
    expect(hits("encode_row(_)")).toEqual(["encode_row_empty"]);
    expect(hits("ode_row(_)")).toEqual([]);
    expect(hits("shape.numel(_)")).toEqual(["reduce_numel"]);
    expect(hits("Queue.peek(Queue.empty(_))")).toEqual(["peek_empty"]);
  });
  test("a bare name finds every statement that mentions it", () => {
    expect(hits("List.length")).toEqual(["length_append"]);
    expect(hits("None")).toEqual(["peek_empty"]);
  });
  test("auto mode treats a dotted name as a shape, as the search help promises", () => {
    expect(looksLikeShape("List.length")).toBe(true);
    expect(looksLikeShape(" Csv.encode_row ")).toBe(true);
    expect(looksLikeShape("List.append(_, Nil{})")).toBe(true);
  });
  test("planted negative: plain words, and several dotted words, stay a names-and-docs search", () => {
    expect(looksLikeShape("add_comm")).toBe(false);
    expect(looksLikeShape("reverse twice")).toBe(false);
    expect(looksLikeShape("List.length List.append")).toBe(false);
    expect(looksLikeShape("v1.2")).toBe(false);
  });
  test("literals and operators must match exactly", () => {
    expect(hits("Nat.add(_, 1n)")).toEqual([]);
    expect(hits("Nat.mul(_, 1n)")).toEqual(["mul_one"]);
    expect(hits('_ == ""')).toEqual(["encode_row_empty"]);
  });
  test("malformed queries are refused with a reason", () => {
    expect(() => compile("List.append(_, Nil{}")).toThrow(ShapeError);
    expect(() => compile("f(x]")).toThrow(ShapeError);
    expect(() => compile("   ")).toThrow(ShapeError);
  });
});
