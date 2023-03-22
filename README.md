# Busy Beaver DFA Decider

This is an implementation of a vertifier for the [bbchallenge project](https://bbchallenge.org/) written in [Dafny](https://dafny.org/).
Dafny is a verification-aware programming language which makes it possible to prove high-level properties about programs using a built-in property checker.

The punchline is being able to write down the following generic function:

```dafny
method verifyDfaPropertiesForProgram<V(!new, ==)>(program: Program, dfa: DFA<V>, initialVertex: V, sinkAccept: V, sinkReject: V) returns (isOkay: bool)
  ensures isOkay ==> programLoopsForever(program)
{
  /* ... */
}
```

where `Program` represents a Turing Machine program with 5 states, `dfa` is a [Deterministic Finite Automaton](https://en.wikipedia.org/wiki/Deterministic_finite_automaton) over the language of "tape strings", `initialVertex` is the vertex to start from, `sinkAccept` is an accepting "sink" vertex, and `sinkReject` is a rejecting "sink" vertex.

If this method returns `true`, then the `ensures` clause guarantees that the `programLoopsForever`.
Dafny has checked over this code and confirmed that there aren't any logical bugs (at least, assuming that the specification of `programLoopsForever` is correct).

## Tape Alphabet and Rewrite Rules

To verify that a program does not halt, this decider treats the Turing Machine's evolution as a string-rewriting system.

The alphabet consists of the following 13 symbols:

- `0`
- `1`
- `$`
- `[A0]`
- `[A1]`
- `[B0]`
- `[B1]`
- `[C0]`
- `[C1]`
- `[D0]`
- `[D1]`
- `[E0]`
- `[E1]`

(note that although `[A0]` is written out for clarity here as 4 characters, it is a single symbol on the tape)

Given a machine like [`1RB1LD_1RC0LB_1RD---_1LA0RE_0LA1RE`](https://bbchallenge.org/13173740), whose rule transition table looks like:

```
	 0   1
A	1RB	1LD
B	1RC	0LB
C	1RD	---
D	1LA	0RE
E	0LA	1RE
```

we construct a set of rewrite rules:

- `[A0]0 --> 1[B0]`
- `[A0]1 --> 1[B1]`
- `[A0]$ --> 1[B0]$`
- `0[A1] --> [D0]1`
- `1[A1] --> [D1]1`
- `$[A1] --> $[D0]1`
- `[B0]0 --> 1[C0]`
- `[B0]1 --> 1[C1]`
- `[B0]$ --> 1[C0]$`
- `0[B1] --> [B0]0`
- `1[B1] --> [B1]0`
- `$[B1] --> $[B0]0`
- `[C0]0 --> 1[D0]`
- `[C0]1 --> 1[D1]`
- `[C0]$ --> 1[D0]$`
- `0[D0] --> [A0]1`
- `1[D0] --> [A1]1`
- `$[D0] --> $[A0]1`
- `[D1]0 --> 0[E0]`
- `[D1]1 --> 0[E1]`
- `[D1]$ --> 0[E0]$`
- `0[E0] --> [A0]0`
- `1[E0] --> [A1]0`
- `$[E0] --> $[A0]0`
- `[E1]0 --> 1[E0]`
- `[E1]1 --> 1[E1]`
- `[E1]$ --> 1[E0]$`

Each rule corresponds to a single step of the Turing Machine configuration, starting from a "blank" tape of `$[A0]$`.

If, starting from the initial string `$[A0]$`, every string has a successor, then the corresponding Turing Machine program does not halt on initially-blank input.

## Verifier Overview

A DFA specifies an (infinite) set of tape strings: a string `s` "matches" the DFA if, starting from the initial vertex, following the edge marked by each symbol in `s` finally lands on a vertex marked "accept".

In the Dafny source, we define this as

```dafny
function followStringFrom<Vertex>(d: WholeDFA<Vertex>, tape: TapeString, from: Vertex): (answer: Vertex)
  requires from in d.follow
  ensures answer in d.follow {
  if |tape| == 0 then from else
  reveal wholeDfa();
  followStringFrom(d, tape[1..], d.follow[from][tape[0]])
}

predicate stringMatchesDFAFrom<Vertex>(d: WholeDFA<Vertex>, tape: TapeString, from: Vertex)
  requires from in d.follow
{
  followStringFrom(d, tape, from) in d.accept
}
```

Given such a dfa `d`, write `L(d)` to mean its language (the set of all strings that it accepts).
If this language `L` satisfies the following properties:

- `"$[A0]$" in L`
- if `X --> Y` is a program rewrite rule and the string `AXB` is in `L`, then `AYB` is also in `L`
- every string in `L` contains exactly one "head" symbol (`[A0]`, `[A1]`, `[B0]`, `[B1]`, ...)
- no string in `L` contains a terminating "head" symbol (in the above program, only `[C1]`)

then the corresponding Turing Machine does not halt starting on blank input.

The verifier is built from several functions that check each of these properties.

## Building and Running the Verified

TODO
