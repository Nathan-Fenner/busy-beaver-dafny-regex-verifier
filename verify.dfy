// This decider combines two other deciders:
// - First, a (forward version of) Halting Segment, described in https://discuss.bbchallenge.org/t/decider-halting-segment/75.
// - Second, a "Nearby Segment" domain, which tracks only cells near the head tape.
// Each abstract state is a pair of (halting_segment, nearby_segment), and pairs whose values are incompatible can be pruned.

// A bit is either 0 or 1.
datatype Bit = B0 | B1

// Because the word "state" would otherwise be overloaded, the 5 "states" for the
// TM are instead called "Colors": CA, CB, CC, CD, CE, with the "C" standing for "State".
datatype State = CA | CB | CC | CD | CE

datatype MachineConfig = MachineConfig(
  tape: set<int>, // The set of 1s
  position: int,
  color: State
)

// The TM can move left or right at each step.
datatype Direction = L | R

function offsetOfDirection(d: Direction): int {
  if d == R then 1 else -1
}

// An action describes what the machine might be told to do by a program:
// - write the given bit
// - switch to the given color
// - move one step in given direction
datatype Action = Action(write: Bit, nextState: State, move: Direction)

// configStepAction applies the given action to the machine state.
function configStepAction(m: MachineConfig, action: Action): MachineConfig {
  MachineConfig(
    tape := if action.write == B1 then m.tape + {m.position} else m.tape - {m.position},
    position := m.position + offsetOfDirection(action.move),
    color := action.nextState
  )
}

// All TMs are assumed to begin in the color CA, on a tape of all zeros.
const InitialMachineConfig: MachineConfig := MachineConfig(
                                               tape := {},
                                               position := 0,
                                               color := CA
                                             )

// `Input` is a structure containing the information needed to find out what
// action should be applied next in a TM program.
datatype Input = Input(head: Bit, color: State)

// A program is a (partial) mapping from inputs to actions, describing what the TM
// should do next in each situation.
//
// If a transition is absent, then it is assumed to be a halting transition.
type Program = map<Input, Action>

// A `MachineStep` either is either `Halt` if no transition for the current state
// exists, or it is NextConfig and holds that next state.
datatype MachineStep = NextConfig(nextConfig: MachineConfig) | Halt

function configInput(c: MachineConfig): Input {
  Input(if c.position in c.tape then B1 else B0, c.color)
}

// configStep causes the provided state to step forward once according to the
// provided program. The output will either be the next state, or Halt if there
// is no configured transition.
function configStep(program: Program, c: MachineConfig): MachineStep {
  var input := configInput(c);
  if input in program
  then NextConfig(configStepAction(c, program[input]))
  else Halt
}

// This function is a helper for moving 'n' steps forward in time.
// It is a `function` rather than `function` because it will cause stack-overflow if run
// for more than a small number of iterations.
function configStepN(program: Program, m: MachineConfig, n: nat): MachineStep {
  if n == 0
  // If n is zero, then the output is the same as the initial program.
  then NextConfig(m)
  // Otherwise, run n-1 steps. If that machine has not yet halted, run it one
  // more step.
  else match configStepN(program, m, n-1) {
      case Halt => Halt
      case NextConfig(m2) => configStep(program, m2)
    }
}

// This method computes the same value as `configStepN` (guaranteed by its ensures clause below).
// This version can be called at runtime because it will not overflow the stack.
method configStepIterative(program: Program, m: MachineConfig, n: nat)
  returns (result: MachineStep)
  ensures result == configStepN(program, m, n) {
  var i := 0;
  var current_state := NextConfig(m);

  while i < n
    invariant 0 <= i <= n
    invariant current_state == configStepN(program, m, i)
  {
    current_state := if current_state.Halt? then Halt else configStep(program, current_state.nextConfig);
    i := i + 1;
  }
  return current_state;
}

// This function returns the nth TM state for a program, starting from the
// initial state.
function programConfigIter(program: Program, n: nat): MachineStep {
  configStepN(program, InitialMachineConfig, n)
}

// By definition, a machine halts if there's a step such that at that point, it halts.
ghost predicate programEventuallyHalts(program: Program) {
  exists n :: n >= 0 && programConfigIter(program, n).Halt?
}

// A program loops forever if it never halts.
ghost predicate programLoopsForever(program: Program) {
  !programEventuallyHalts(program)
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////

function stateFromChar(s: char): State {
  match s {
    case 'A' => CA
    case 'B' => CB
    case 'C' => CC
    case 'D' => CD
    case 'E' => CE
    case _ => CA // Avoid
  }
}

function bitFromChar(s: char): Bit {
  match s {
    case '0' => B0
    case '1' => B1
    case _ => B0 // Avoid
  }
}

function dirFromChar(s: char): Direction {
  match s {
    case 'R' => R
    case 'L' => L
    case _ => R // Avoid
  }
}

method programFromString(desc: string) returns (program: Program)
  requires |desc| == 34 {
  program := map[];
  var col: State;
  var base: nat;

  base := 0;
  col := CA;
  if desc[base] != '-' {
    program := program[Input(B0, col) := Action(bitFromChar(desc[base]), stateFromChar(desc[base+2]), dirFromChar(desc[base+1]))];
  }
  if desc[base+3] != '-' {
    program := program[Input(B1, col) := Action(bitFromChar(desc[base+3]), stateFromChar(desc[base+5]), dirFromChar(desc[base+4]))];
  }
  base := 7;
  col := CB;
  if desc[base] != '-' {
    program := program[Input(B0, col) := Action(bitFromChar(desc[base]), stateFromChar(desc[base+2]), dirFromChar(desc[base+1]))];
  }
  if desc[base+3] != '-' {
    program := program[Input(B1, col) := Action(bitFromChar(desc[base+3]), stateFromChar(desc[base+5]), dirFromChar(desc[base+4]))];
  }
  base := 14;
  col := CC;
  if desc[base] != '-' {
    program := program[Input(B0, col) := Action(bitFromChar(desc[base]), stateFromChar(desc[base+2]), dirFromChar(desc[base+1]))];
  }
  if desc[base+3] != '-' {
    program := program[Input(B1, col) := Action(bitFromChar(desc[base+3]), stateFromChar(desc[base+5]), dirFromChar(desc[base+4]))];
  }
  base := 21;
  col := CD;
  if desc[base] != '-' {
    program := program[Input(B0, col) := Action(bitFromChar(desc[base]), stateFromChar(desc[base+2]), dirFromChar(desc[base+1]))];
  }
  if desc[base+3] != '-' {
    program := program[Input(B1, col) := Action(bitFromChar(desc[base+3]), stateFromChar(desc[base+5]), dirFromChar(desc[base+4]))];
  }
  base := 28;
  col := CE;
  if desc[base] != '-' {
    program := program[Input(B0, col) := Action(bitFromChar(desc[base]), stateFromChar(desc[base+2]), dirFromChar(desc[base+1]))];
  }
  if desc[base+3] != '-' {
    program := program[Input(B1, col) := Action(bitFromChar(desc[base+3]), stateFromChar(desc[base+5]), dirFromChar(desc[base+4]))];
  }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////

datatype TapeAlpha = TapeBit(tapeBit: Bit) | TapeHead(tapeHeadState: State, tapeHeadBit: Bit) | TapeEnd

predicate bitIsOne(a: TapeAlpha) {
  match a
  case TapeBit(b) => b == B1
  case TapeHead(_, bh) => bh == B1
  case TapeEnd => false
}

type TapeString = seq<TapeAlpha>

predicate regularTape(tape: seq<TapeAlpha>) {
  |tape| >= 3 && tape[0] == TapeEnd &&
  tape[|tape|-1] == TapeEnd &&
  exists i ::
    1 <= i < |tape|-1 && tape[i].TapeHead? &&
    forall j | (1 <= j < |tape|-1 && j != i) :: tape[j].TapeBit?
}

datatype RewriteRule = MkRewriteRule(before: TapeString, after: TapeString)

function performRewriteAt(s: TapeString, rule: RewriteRule, at: nat): (r: TapeString)
  requires 0 <= at <= |s| - |rule.before|
  requires s[at .. at + |rule.before|] == rule.before
{
  s[..at] + rule.after + s[at+|rule.before|..]
}

function singleHeadTrigger(i: nat): nat { 0 }

predicate {:opaque true} elsewhereAreBits(tape: TapeString, headIndex: nat)
  requires 0 <= headIndex < |tape|
{
  forall i | 0 <= i < |tape| && i != headIndex :: tape[i].TapeBit?
}

predicate {:opaque true} singleHead(tape: TapeString) {
  exists headIndex :: 0 <= headIndex < |tape| && tape[headIndex].TapeHead? && elsewhereAreBits(tape, headIndex)
}

lemma singleHeadIndexWorksIndex(tape: TapeString, r: nat, j: nat)
  requires singleHead(tape)
  requires 0 <= r < |tape| && tape[r].TapeHead?;
  requires 0 <= j < |tape| && j != r
  ensures tape[j].TapeBit?
{
  reveal singleHead();
  reveal elsewhereAreBits();
  assert singleHeadTrigger(j) == 0;
  var headIndex :| 0 <= headIndex < |tape| && tape[headIndex].TapeHead? && (forall i | 0 <= i < |tape| && i != headIndex :: tape[i].TapeBit?);
}

lemma singleHeadIndexWorks(tape: TapeString, r: nat)
  requires singleHead(tape)
  requires 0 <= r < |tape| && tape[r].TapeHead?
  ensures elsewhereAreBits(tape, r)
{
  reveal elsewhereAreBits();
  forall j | 0 <= j < |tape| && j != r ensures tape[j].TapeBit? {
    singleHeadIndexWorksIndex(tape, r, j);
  }
}

ghost function singleHeadIndex(tape: TapeString): (r: nat)
  requires singleHead(tape)
  ensures 0 <= r < |tape|
  ensures tape[r].TapeHead? && elsewhereAreBits(tape, r)
{
  reveal singleHead();
  var out :| 0 <= out < |tape| && tape[out].TapeHead?;
  singleHeadIndexWorks(tape, out);
  out
}

predicate singleHeadRule(rule: RewriteRule)
  decreases |rule.before| {
  ( // If they have a common ending...
  |rule.before| >= 2 &&
  |rule.after| >= 2 &&
  rule.before[|rule.before|-1] == rule.after[|rule.after|-1] &&
  |rule.after| >= |rule.before| &&
  singleHeadRule(MkRewriteRule(rule.before[..|rule.before|-1], rule.after[..|rule.after|-1]))
  ) ||
  ( // Or a common beginning...
  |rule.before| >= 2 &&
  |rule.after| >= 2 &&
  rule.before[0] == rule.after[0] &&
  |rule.after| >= |rule.before| &&
  singleHeadRule(MkRewriteRule(rule.before[1..], rule.after[1..]))
  ) ||
  (singleHead(rule.before) && singleHead(rule.after))
}

lemma singleHeadRulesPreservesRegularityAt(tape: TapeString, rule: RewriteRule, at: nat)
  decreases |rule.before|
  requires regularTape(tape)
  requires singleHeadRule(rule)
  requires 0 <= at <= |tape| - |rule.before|
  requires |rule.before| > 0
  requires tape[at .. at + |rule.before|] == rule.before
  ensures regularTape(performRewriteAt(tape, rule, at))
{

  var rewritten := performRewriteAt(tape, rule, at);
  assert |rewritten| == at + |rule.after| + |tape[at + |rule.before|..]|;

  reveal singleHead();

  if |rule.before| >= 2 &&
     |rule.after| >= 2 &&
     rule.before[|rule.before|-1] == rule.after[|rule.after|-1] &&
     |rule.after| >= |rule.before| &&
     singleHeadRule(MkRewriteRule(rule.before[..|rule.before|-1], rule.after[..|rule.after|-1]))
  {
    assert |rewritten| >= 3;
    var shrinkRule := MkRewriteRule(rule.before[..|rule.before|-1], rule.after[..|rule.after|-1]);
    singleHeadRulesPreservesRegularityAt(tape, shrinkRule, at);
    assert performRewriteAt(tape, shrinkRule, at) == rewritten;
    assert regularTape(rewritten);
    return;
  }

  if |rule.before| >= 2 &&
     |rule.after| >= 2 &&
     rule.before[0] == rule.after[0] &&
     |rule.after| >= |rule.before| &&
     singleHeadRule(MkRewriteRule(rule.before[1..], rule.after[1..]))
  {
    assert |rewritten| >= 3;
    var shrinkRule := MkRewriteRule(rule.before[1..], rule.after[1..]);
    singleHeadRulesPreservesRegularityAt(tape, shrinkRule, at+1);
    assert performRewriteAt(tape, shrinkRule, at+1) == rewritten;
    assert regularTape(rewritten);
    return;
  }

  reveal elsewhereAreBits();

  assert singleHeadTrigger(0) == 0;
  assert rule.before[0] != TapeEnd;
  assert |rewritten| == at + |rule.after| + |tape[at + |rule.before|..]|;
  assert at >= 1;
  assert |rule.after| >= 1;
  assert singleHeadTrigger(|rule.before|-1) == 0;
  assert rule.before[|rule.before|-1] != TapeEnd;
  assert |rewritten| >= 3;
  assert rewritten[0] == TapeEnd;
  assert rewritten[|rewritten|-1] == TapeEnd;

  var ruleBeforeHeadIndex := singleHeadIndex(rule.before);
  var ruleAfterHeadIndex := singleHeadIndex(rule.after);

  assert rule.after[ruleAfterHeadIndex].TapeHead?;
  assert rewritten == tape[..at] + rule.after + tape[at + |rule.before|..];
  assert rewritten[at + ruleAfterHeadIndex] == rule.after[ruleAfterHeadIndex];

  forall j | 1 <= j < |rewritten|-1 && j != at + ruleAfterHeadIndex ensures rewritten[j].TapeBit? {
    if j < at {
      assert rewritten[j].TapeBit?;
    } else if j < at + |rule.after| {
      assert j != at + ruleAfterHeadIndex;
      assert rewritten[j] == rule.after[j - at];
      assert rewritten[j].TapeBit?;
    } else {
      assert rewritten[j] == tape[j - |rule.after| + |rule.before|];
      assert rewritten[j].TapeBit?;
    }
  }

  assert regularTape(rewritten);
}

datatype DFA<Vertex(==)> = MkDFA(
  follow: map<Vertex, map<TapeAlpha, Vertex>>,
  vertexList: seq<Vertex>,
  accept: set<Vertex>
)

ghost predicate {:opaque true} wholeDfa<Vertex>(dfa: DFA<Vertex>) {
(forall v | v in dfa.follow :: forall x :: x in dfa.follow[v] && dfa.follow[v][x] in dfa.follow)
  &&
(forall v | v in dfa.follow :: v in dfa.follow <==> v in dfa.vertexList)
  &&
(forall v | v in dfa.vertexList :: v in dfa.follow <==> v in dfa.vertexList)
}

lemma wholeDfaVertexEquivalence<Vertex>(dfa: WholeDFA<Vertex>)
  ensures (forall v | v in dfa.follow :: v in dfa.follow <==> v in dfa.vertexList)
  ensures (forall v | v in dfa.vertexList :: v in dfa.follow <==> v in dfa.vertexList)
{
  reveal wholeDfa();
}

lemma wholeDfaWorks<V>(d: WholeDFA<V>, a: V, x: TapeAlpha) requires a in d.follow ensures x in d.follow[a] && d.follow[a][x] in d.follow {
  reveal wholeDfa();
}

type WholeDFA<Vertex> = dfa: DFA | wholeDfa(dfa) witness *

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

lemma stringMatchesDFAFromEventually<Vertex>(d: WholeDFA<Vertex>, tape: TapeString, from: Vertex, index: nat)
  requires from in d.follow
  requires 0 <= index <= |tape|
  ensures stringMatchesDFAFrom(d, tape, from) <==> stringMatchesDFAFrom(d, tape[index..], followStringFrom(d, tape[..index], from))
{
  if index == 0 {
    // ... done
  } else {
    wholeDfaWorks(d, from, tape[0]);
    var nextV := d.follow[from][tape[0]];
    assert stringMatchesDFAFrom(d, tape, from) <==> stringMatchesDFAFrom(d, tape[1..], nextV);
    stringMatchesDFAFromEventually(d, tape[1..], nextV, index-1);
    assert tape[1..index] == tape[1..][..index-1];
  }
}

lemma stringMatchesSink<Vertex>(d: WholeDFA<Vertex>, tape: TapeString, sink: Vertex)
  requires sink in d.follow
  requires forall x: TapeAlpha :: sink in d.follow && x in d.follow[sink] && d.follow[sink][x] == sink
  ensures stringMatchesDFAFrom(d, tape, sink) <==> sink in d.accept
{
  if |tape| == 0 {
    // done
  } else {
    wholeDfaWorks(d, sink, tape[0]);
    stringMatchesSink(d, tape[1..], sink);
  }
}

// This is a utility method which checks (at runtime) that a predicate
// holds for each element of a set.
// If it does, it returns true, otherwise it returns false.
method checkAll<T(!new)>(domain: set<T>, func: T --> bool)
  returns (okay: bool)
  requires forall x | x in domain :: func.requires(x)
  ensures okay ==> forall x | x in domain :: func(x)
{
  var leftover := domain;
  while |leftover| > 0 invariant forall x | x in domain :: func(x) || x in leftover
    invariant forall x | x in leftover :: x in domain {
    var x :| x in leftover;
    assert x in domain;
    var itemOkay := func(x);
    if !itemOkay {
      return false;
    }
    leftover := leftover - {x};
  }
  return true;
}

ghost predicate {:opaque true} funcForAll<T>(domain: seq<T>, func: T --> bool)
  requires forall x | x in domain :: func.requires(x)
{
  forall x | x in domain :: func(x)
}

lemma {:opaque true} instanceFuncForAll<T>(domain: seq<T>, func: T --> bool, x: T)
  requires forall x | x in domain :: func.requires(x)
  requires funcForAll(domain, func)
  requires x in domain
  ensures func(x)
{
  reveal funcForAll();
}

function {:opaque true} checkAllRecursive<T(!new)>(domain: seq<T>, func: T --> bool): (okay: bool)
  requires forall x | x in domain :: func.requires(x)
  ensures okay ==> funcForAll(domain, func)
{
  reveal funcForAll();
  if |domain| == 0 then true else
  func(domain[0]) && checkAllRecursive(domain[1..], func)
}

ghost predicate {:opaque} vertexSubsumption<Vertex>(d: WholeDFA<Vertex>, a: Vertex, b: Vertex)
  requires a in d.follow
  requires b in d.follow {
  forall tape | stringMatchesDFAFrom(d, tape, a) :: stringMatchesDFAFrom(d, tape, b)
}

// Dafny does not know this fact:
// https://github.com/dafny-lang/dafny/issues/224
lemma {:opaque true} subsetIsSmaller<T>(smaller: set<T>, bigger: set<T>)
  requires smaller <= bigger
  ensures |smaller| <= |bigger|
{
  if |smaller| == 0 {
    // Done!
  } else {
    var x :| x in smaller;
    subsetIsSmaller(smaller - {x}, bigger - {x});
  }
}

predicate triggerPairInAcceptFollow<V>(a: V, b: V) { true }
predicate triggerPairInNext<V>(p: (V, V)) { true }

predicate {:opaque true} pairsInFollow<V>(d: WholeDFA<V>, pairs: set<(V, V)>)
{
  forall p | p in pairs :: p.0 in d.follow && p.1 in d.follow
}

lemma applyPairsInFollow<V>(d: WholeDFA<V>, pairs: set<(V, V)>, p: (V, V))
  requires pairsInFollow(d, pairs)
  requires p in pairs
  ensures p.0 in d.follow
  ensures p.1 in d.follow
{
  reveal pairsInFollow();
}

lemma applyPairsInFollowSym<V>(d: WholeDFA<V>, pairs: set<(V, V)>, p: (V, V), x: TapeAlpha)
  requires pairsInFollow(d, pairs)
  requires p in pairs
  ensures p.0 in d.follow
  ensures p.1 in d.follow
  ensures x in d.follow[p.0]
  ensures x in d.follow[p.1]
{
  reveal pairsInFollow();
  reveal wholeDfa();
}

predicate {:opaque true} pairsInAccept<V>(d: WholeDFA<V>, pairs: set<(V, V)>)
  requires pairsInFollow(d, pairs)
{
  reveal pairsInFollow();
  forall a, b {:trigger triggerPairInAcceptFollow(a, b)} | a in d.follow && b in d.follow && a in d.accept && b !in d.accept :: (a, b) !in pairs
}

lemma {:opaque true} applyPairsInAccept<V>(d: WholeDFA<V>, pairs: set<(V, V)>, a: V, b: V)
  requires (a, b) in pairs
  requires pairsInFollow(d, pairs)
  requires pairsInAccept(d, pairs)
  ensures a in d.accept ==> b in d.accept
{
  reveal pairsInFollow();
  reveal pairsInAccept();
  assert triggerPairInAcceptFollow(a, b);
}

predicate triggerPairsInNextAlpha<V>(p: (V, V), x: TapeAlpha) { true }

ghost predicate {:opaque true} pairsInNext<V(!new)>(d: WholeDFA<V>, pairs: set<(V, V)>)
  requires pairsInFollow(d, pairs) {
  reveal wholeDfa();
  reveal pairsInFollow();
  forall p {:trigger triggerPairInNext(p)} | p in pairs :: forall x: TapeAlpha {:trigger triggerPairsInNextAlpha(p, x)} :: (d.follow[p.0][x], d.follow[p.1][x]) in pairs
}

lemma {:opaque true} applyPairsInNext<V>(d: WholeDFA<V>, pairs: set<(V, V)>, a: V, b: V, x: TapeAlpha)
  requires pairsInFollow(d, pairs)
  requires pairsInNext(d, pairs)
  requires (a, b) in pairs
  ensures reveal wholeDfa(); a in d.follow && b in d.follow && (d.follow[a][x], d.follow[b][x]) in pairs
{
  reveal pairsInFollow();
  reveal pairsInNext();
  assert triggerPairInNext((a, b));
  assert triggerPairsInNextAlpha((a, b), x);
}

predicate triggerPairsInFollow<V>(p: (V, V)) { true }

lemma {:opaque true} computeDfaAcceptanceSubsetsInduction<V>(d: WholeDFA<V>, pairs: set<(V, V)>, a: V, b: V, tape: TapeString)
  decreases |tape|
  requires pairsInFollow(d, pairs)
  requires pairsInAccept(d, pairs)
  requires pairsInNext(d, pairs)
  requires a in d.follow
  requires b in d.follow
  requires (a, b) in pairs
  requires stringMatchesDFAFrom(d, tape, a)
  ensures stringMatchesDFAFrom(d, tape, b)
{
  if |tape| == 0 {
    assert a in d.accept;
    applyPairsInAccept(d, pairs, a, b);
    assert stringMatchesDFAFrom(d, tape, b);
  } else {
    reveal wholeDfa();
    var x := tape[0];
    applyPairsInNext(d, pairs, a, b, x);
    var a2 := d.follow[a][x];
    var b2 := d.follow[b][x];
    assert (a2, b2) in pairs;
    assert stringMatchesDFAFrom(d, tape[1..], a2);
    assert a2 in d.follow;
    assert b2 in d.follow;
    assert |tape[1..]| < |tape|;
    computeDfaAcceptanceSubsetsInduction(d, pairs, a2, b2, tape[1..]);
  }
}

function {:opaque true} dfaAcceptedSubsetExcludeTerminal<V(!new)>(pairs: set<(V, V)>, accept: set<V>): (newExclude: set<(V, V)>)
  ensures newExclude <= pairs {
  (set p | p in pairs && var a := p.0; var b := p.1; a in accept && b !in accept)
}

lemma {:opaque true} methodAllTapeAlphaWorks() ensures forall a: TapeAlpha :: a in methodAllTapeAlpha() {
  forall a: TapeAlpha
    ensures a in methodAllTapeAlpha()
  {
    assert a.TapeBit? || a.TapeEnd? || a.TapeHead?;
    assert a.TapeEnd? ==> a == TapeEnd;
    assert a.TapeBit? ==> a.tapeBit.B0? || a.tapeBit.B1?;
    assert a.TapeBit? ==> a == TapeBit(B0) || a == TapeBit(B1);
    assert a.TapeHead? ==> a.tapeHeadBit.B0? || a.tapeHeadBit.B1?;
    assert a.TapeHead? ==> a.tapeHeadState.CA? || a.tapeHeadState.CB? || a.tapeHeadState.CC? || a.tapeHeadState.CD? || a.tapeHeadState.CE?;
    assert a.TapeHead? ==> a.tapeHeadBit == B0 || a.tapeHeadBit == B1;
    assert a.TapeHead? ==>
        a == TapeHead(CA, B0) ||
        a == TapeHead(CA, B1) ||
        a == TapeHead(CB, B0) ||
        a == TapeHead(CB, B1) ||
        a == TapeHead(CC, B0) ||
        a == TapeHead(CC, B1) ||
        a == TapeHead(CD, B0) ||
        a == TapeHead(CD, B1) ||
        a == TapeHead(CE, B0) ||
        a == TapeHead(CE, B1);
  }
}

function methodAllTapeAlpha(): (r: set<TapeAlpha>)
{
  {
    TapeBit(B0),
    TapeBit(B1),
    TapeEnd,
    TapeHead(CA, B0),
    TapeHead(CA, B1),

    TapeHead(CB, B0),
    TapeHead(CB, B1),

    TapeHead(CC, B0),
    TapeHead(CC, B1),

    TapeHead(CD, B0),
    TapeHead(CD, B1),

    TapeHead(CE, B0),
    TapeHead(CE, B1)
  }
}

predicate excludeChainedBitTrigger<V>(p: (V, V), x: TapeAlpha) { true }

function {:opaque true} dfaAcceptedSubsetExcludeChainedBit<V(!new)>(pairs: set<(V, V)>, d: WholeDFA<V>): (newExclude: set<(V, V)>)
  requires pairsInFollow(d, pairs)
  ensures newExclude <= pairs
{
  var allSym := methodAllTapeAlpha();
  methodAllTapeAlphaWorks();
  reveal wholeDfa();
  reveal pairsInFollow();
  (set p, sym {:trigger excludeChainedBitTrigger(p, sym)} | sym in allSym && p in pairs && var a := p.0; var b := p.1; (d.follow[a][sym], d.follow[b][sym]) !in pairs :: p)
}

lemma {:opaque true} applySubsetExcludeChainedBit<V(!new)>(d: WholeDFA<V>, pairs: set<(V, V)>, p: (V, V), x: TapeAlpha)
  requires p in pairs
  requires pairsInFollow(d, pairs)
  requires dfaAcceptedSubsetExcludeChainedBit(pairs, d) == {}
  ensures p.0 in d.follow && p.1 in d.follow && x in d.follow[p.0] && x in d.follow[p.1]
  ensures (d.follow[p.0][x], d.follow[p.1][x]) in pairs
{
  applyPairsInFollowSym(d, pairs, p, x);
  reveal dfaAcceptedSubsetExcludeChainedBit();
  assert excludeChainedBitTrigger(p, x);
  var q := (d.follow[p.0][x], d.follow[p.1][x]);

  var allSym := methodAllTapeAlpha();
  methodAllTapeAlphaWorks();
  assert x in allSym;

  assert p in pairs && q !in pairs ==> p in dfaAcceptedSubsetExcludeChainedBit(pairs, d);
}

ghost predicate {:opaque true} pairsAreSubsumed<V>(d: WholeDFA<V>, pairs: set<(V, V)>)
  requires pairsInFollow(d, pairs)
{
  reveal pairsInFollow();
  forall p | p in pairs :: vertexSubsumption(d, p.0, p.1)
}


lemma pairsAreValidSingleInduction<V(!new)>(d: WholeDFA<V>, pairs: set<(V, V)>, p: (V, V), tape: TapeString)
  decreases |tape|
  requires pairsInFollow(d, pairs)
  requires dfaAcceptedSubsetExcludeTerminal(pairs, d.accept) == {}
  requires dfaAcceptedSubsetExcludeChainedBit(pairs, d) == {}
  requires p in pairs
  requires reveal pairsInFollow(); stringMatchesDFAFrom(d, tape, p.0)
  ensures stringMatchesDFAFrom(d, tape, p.1)
{
  applyPairsInFollow(d, pairs, p);
  if |tape| == 0 {
    assert p.0 in d.accept;
    reveal dfaAcceptedSubsetExcludeTerminal();
    assert p.0 in d.accept && p.1 !in d.accept ==> p in dfaAcceptedSubsetExcludeTerminal(pairs, d.accept);
    assert p.1 in d.accept;
    assert stringMatchesDFAFrom(d, tape, p.1);
  } else {
    applyPairsInFollowSym(d, pairs, p, tape[0]);
    var q := (d.follow[p.0][tape[0]], d.follow[p.1][tape[0]]);
    applySubsetExcludeChainedBit(d, pairs, p, tape[0]);
    assert q in pairs;
    pairsAreValidSingleInduction(d, pairs, q, tape[1..]);
  }
}

lemma pairsAreValidSingle<V(!new)>(d: WholeDFA<V>, pairs: set<(V, V)>, p: (V, V))
  requires pairsInFollow(d, pairs)
  requires dfaAcceptedSubsetExcludeTerminal(pairs, d.accept) == {}
  requires dfaAcceptedSubsetExcludeChainedBit(pairs, d) == {}
  requires p in pairs
  ensures reveal pairsInFollow(); vertexSubsumption(d, p.0, p.1)
{
  reveal pairsInFollow();
  reveal vertexSubsumption();
  forall tape | stringMatchesDFAFrom(d, tape, p.0) ensures reveal pairsInFollow(); stringMatchesDFAFrom(d, tape, p.1) {
    pairsAreValidSingleInduction(d, pairs, p, tape);
  }
}

lemma pairsAreValid<V(!new)>(d: WholeDFA<V>, pairs: set<(V, V)>)
  requires pairsInFollow(d, pairs)
  requires dfaAcceptedSubsetExcludeTerminal(pairs, d.accept) == {}
  requires dfaAcceptedSubsetExcludeChainedBit(pairs, d) == {}
  ensures pairsAreSubsumed(d, pairs)
{
  reveal pairsAreSubsumed();
  forall p | p in pairs ensures reveal pairsInFollow(); vertexSubsumption(d, p.0, p.1) {
    pairsAreValidSingle(d, pairs, p);
  }
}


method {:opaque true} computeDfaAcceptanceSubsets<V(!new, ==)>(d: WholeDFA<V>) returns (pairs: set<(V, V)>)
  ensures pairsInFollow(d, pairs)
  ensures pairsAreSubsumed(d, pairs)
{
  reveal pairsInFollow();
  var allVertexPairs: set<(V, V)> := set a, b | a in d.follow && b in d.follow :: (a, b);

  pairs := allVertexPairs;

  // Whittle away the invalid pairs, until we're left with a valid core.

  while dfaAcceptedSubsetExcludeTerminal(pairs, d.accept) != {}
    || dfaAcceptedSubsetExcludeChainedBit(pairs, d) != {}
    invariant pairs <= allVertexPairs
    invariant pairsInFollow(d, pairs)
    decreases |pairs|
  {
    pairs := pairs
    - dfaAcceptedSubsetExcludeTerminal(pairs, d.accept)
    - dfaAcceptedSubsetExcludeChainedBit(pairs, d)
      ;
  }

  assert dfaAcceptedSubsetExcludeTerminal(pairs, d.accept) == {};
  assert dfaAcceptedSubsetExcludeChainedBit(pairs, d) == {};

  pairsAreValid(d, pairs);

  return pairs;
}


////////////////////////////////////////////////////////////////////////////////////////////////
// This next section combines the rewriting logic with the given program.

function regularTapeConfig(str: (int, seq<TapeAlpha>)): MachineConfig
  requires regularTape(str.1) {
  var i :| 1 <= i < |str.1|-1 && str.1[i].TapeHead?;
  MachineConfig(
    position := i + str.0,
    color := str.1[i].tapeHeadState,
    tape := set j | 0 <= j < |str.1| && bitIsOne(str.1[j]) :: j + str.0
  )
}

const InitialTapeString: (int, TapeString) := (-1, [TapeEnd, TapeHead(CA, B0), TapeEnd]);

lemma initialTapeStringIsRegular() ensures regularTape(InitialTapeString.1) {
  var tape := InitialTapeString.1;
  var idx := 1;
  assert tape[idx].TapeHead?;
  assert tape[0].TapeEnd?;
  assert tape[2].TapeEnd?;
}

lemma initialTapeString()
  ensures regularTape(InitialTapeString.1)
  ensures regularTapeConfig(InitialTapeString) == InitialMachineConfig {
  initialTapeStringIsRegular();
}

// [Ah] t --> w [Bt]
lemma rewriteRuleForMoveRightInto(program: Program, input: Input, action: Action, s: (int, TapeString), at: nat, b: Bit)
  requires regularTape(s.1)
  requires input in program
  requires action == program[input]
  requires 0 <= at <= |s.1| - 2
  requires action.move == R
  requires s.1[at .. at + 2] == [TapeHead(input.color, input.head), TapeBit(b)]
  ensures configStep(program, regularTapeConfig(s)).NextConfig?
  ensures
    var rewritten := performRewriteAt(s.1, MkRewriteRule([TapeHead(input.color, input.head), TapeBit(b)], [TapeBit(action.write), TapeHead(action.nextState, b)]), at);
    regularTape(rewritten) &&
    regularTapeConfig((s.0, rewritten)) == configStep(program, regularTapeConfig(s)).nextConfig
{
  var rule := MkRewriteRule([TapeHead(input.color, input.head), TapeBit(b)], [TapeBit(action.write), TapeHead(action.nextState, b)]);
  reveal singleHead();
  reveal elsewhereAreBits();
  assert rule.before[0].TapeHead?;
  forall i | 0 <= i < |rule.before| && i != 0 ensures rule.before[i].TapeBit? {}
  assert singleHead(rule.before);
  assert rule.after[1].TapeHead?;
  forall i | 0 <= i < |rule.after| && i != 1 ensures rule.after[i].TapeBit? {}
  assert singleHead(rule.after);

  var rewritten := performRewriteAt(s.1, rule, at);
  singleHeadRulesPreservesRegularityAt(s.1, rule, at);
  assert regularTape(rewritten);

  var configBefore := regularTapeConfig(s);
  var configStepBefore := configStep(program, configBefore).nextConfig;
  var configAfter := regularTapeConfig((s.0, rewritten));
  assert configAfter.position == configStepBefore.position;
  assert configAfter.color == configStepBefore.color;
  forall x ensures x in configAfter.tape <==> x in configStepBefore.tape {
    if x == configBefore.position {
      assert x in configStepBefore.tape <==> action.write == B1;
      assert x in configAfter.tape <==> rewritten[at] == TapeBit(B1);
      assert x in configAfter.tape <==> x in configStepBefore.tape;
    } else if x == configBefore.position + 1 {
      assert x in configStepBefore.tape <==> x in configBefore.tape;
      assert x in configAfter.tape <==> rewritten[at+1] == TapeHead(action.nextState, B1);
      assert s.1[at+1] == TapeBit(b);
      assert x in configAfter.tape <==> x in configStepBefore.tape;
    } else {
      assert x in configStepBefore.tape <==> x in configBefore.tape;
      assert x in configBefore.tape <==> (0 <= x-s.0 < |s.1| && s.1[x - s.0] == TapeBit(B1));
      assert x in configAfter.tape <==> (0 <= x-s.0 < |s.1| && rewritten[x - s.0] == TapeBit(B1));
      assert x in configAfter.tape <==> x in configStepBefore.tape;
    }
  }
  assert configAfter.tape == configStepBefore.tape;
  assert configAfter == configStepBefore;
}

// [Ah] $ --> w [B0] $
lemma rewriteRuleForMoveRightEnd(program: Program, input: Input, action: Action, s: (int, TapeString), at: nat)
  requires regularTape(s.1)
  requires input in program
  requires action == program[input]
  requires 0 <= at <= |s.1| - 2
  requires action.move == R
  requires s.1[at .. at + 2] == [TapeHead(input.color, input.head), TapeEnd]
  ensures configStep(program, regularTapeConfig(s)).NextConfig?
  ensures
    var rewritten := performRewriteAt(s.1, MkRewriteRule([TapeHead(input.color, input.head), TapeEnd], [TapeBit(action.write), TapeHead(action.nextState, B0), TapeEnd]), at);
    regularTape(rewritten) &&
    regularTapeConfig((s.0, rewritten)) == configStep(program, regularTapeConfig(s)).nextConfig
{
  var rule := MkRewriteRule([TapeHead(input.color, input.head), TapeEnd], [TapeBit(action.write), TapeHead(action.nextState, B0), TapeEnd]);
  reveal singleHead();
  reveal elsewhereAreBits();
  assert rule.before[..|rule.before|-1][0].TapeHead?;
  forall i | 0 <= i < |rule.before|-1 && i != 0 ensures rule.before[i].TapeBit? {}
  assert singleHead(rule.before[..|rule.before|-1]);
  assert rule.after[..|rule.after|-1][1].TapeHead?;
  forall i | 0 <= i < |rule.after|-1 && i != 1 ensures rule.after[i].TapeBit? {}
  assert singleHead(rule.after[..|rule.after|-1]);
  assert singleHeadRule(rule);

  var rewritten := performRewriteAt(s.1, rule, at);
  singleHeadRulesPreservesRegularityAt(s.1, rule, at);
  assert regularTape(rewritten);

  var configBefore := regularTapeConfig(s);
  var configStepBefore := configStep(program, configBefore).nextConfig;
  var configAfter := regularTapeConfig((s.0, rewritten));
  assert configAfter.position == configStepBefore.position;
  assert configAfter.color == configStepBefore.color;
  forall x ensures x in configAfter.tape <==> x in configStepBefore.tape {
    if x == configBefore.position {
      assert x in configStepBefore.tape <==> action.write == B1;
      assert x in configAfter.tape <==> rewritten[at] == TapeBit(B1);
      assert x in configAfter.tape <==> x in configStepBefore.tape;
    } else if x == configBefore.position + 1 {
      assert x in configStepBefore.tape <==> x in configBefore.tape;
      assert x in configAfter.tape <==> rewritten[at+1] == TapeHead(action.nextState, B1);
      assert s.1[at+1] == TapeEnd;
      assert x in configAfter.tape <==> x in configStepBefore.tape;
    } else {
      assert x in configStepBefore.tape <==> x in configBefore.tape;
      assert x in configBefore.tape <==> (0 <= x-s.0 < |s.1| && s.1[x - s.0] == TapeBit(B1));
      assert x in configAfter.tape <==> (0 <= x-s.0 < |s.1| && rewritten[x - s.0] == TapeBit(B1));
      assert x in configAfter.tape <==> x in configStepBefore.tape;
    }
  }
  assert configAfter.tape == configStepBefore.tape;
  assert configAfter == configStepBefore;
}

// t [Ah] --> [Bt] w
lemma rewriteRuleForMoveLeftInto(program: Program, input: Input, action: Action, s: (int, TapeString), at: nat, b: Bit)
  requires regularTape(s.1)
  requires input in program
  requires action == program[input]
  requires 0 <= at <= |s.1| - 2
  requires action.move == L
  requires s.1[at .. at + 2] == [TapeBit(b), TapeHead(input.color, input.head)]
  ensures configStep(program, regularTapeConfig(s)).NextConfig?
  ensures
    var rewritten := performRewriteAt(s.1, MkRewriteRule([TapeBit(b), TapeHead(input.color, input.head)], [TapeHead(action.nextState, b), TapeBit(action.write)]), at);
    regularTape(rewritten) &&
    regularTapeConfig((s.0, rewritten)) == configStep(program, regularTapeConfig(s)).nextConfig
{
  var rule := MkRewriteRule([TapeBit(b), TapeHead(input.color, input.head)], [TapeHead(action.nextState, b), TapeBit(action.write)]);
  reveal singleHead();
  reveal elsewhereAreBits();
  assert rule.before[1].TapeHead?;
  forall i | 0 <= i < |rule.before| && i != 1 ensures rule.before[i].TapeBit? {}
  assert singleHead(rule.before);
  assert rule.after[0].TapeHead?;
  forall i | 0 <= i < |rule.after| && i != 0 ensures rule.after[i].TapeBit? {}
  assert singleHead(rule.after);

  var rewritten := performRewriteAt(s.1, rule, at);
  singleHeadRulesPreservesRegularityAt(s.1, rule, at);
  assert regularTape(rewritten);

  var configBefore := regularTapeConfig(s);
  var configStepBefore := configStep(program, configBefore).nextConfig;
  var configAfter := regularTapeConfig((s.0, rewritten));
  assert configAfter.position == configStepBefore.position;
  assert configAfter.color == configStepBefore.color;
  forall x ensures x in configAfter.tape <==> x in configStepBefore.tape {
    if x == configBefore.position {
      assert x in configStepBefore.tape <==> action.write == B1;
      assert x in configAfter.tape <==> rewritten[at+1] == TapeBit(B1);
      assert x in configAfter.tape <==> x in configStepBefore.tape;
    } else if x == configBefore.position - 1 {
      assert x in configStepBefore.tape <==> x in configBefore.tape;
      assert x in configAfter.tape <==> rewritten[at] == TapeHead(action.nextState, B1);
      assert s.1[at] == TapeBit(b);
      assert x in configAfter.tape <==> x in configStepBefore.tape;
    } else {
      assert x in configStepBefore.tape <==> x in configBefore.tape;
      assert x in configBefore.tape <==> (0 <= x-s.0 < |s.1| && s.1[x - s.0] == TapeBit(B1));
      assert x in configAfter.tape <==> (0 <= x-s.0 < |s.1| && rewritten[x - s.0] == TapeBit(B1));
      assert x in configAfter.tape <==> x in configStepBefore.tape;
    }
  }
  assert configAfter.tape == configStepBefore.tape;
  assert configAfter == configStepBefore;
}

// $ [Ah] --> $ [B0] w
lemma rewriteRuleForMoveLeftEnd(program: Program, input: Input, action: Action, s: (int, TapeString), at: nat)
  requires regularTape(s.1)
  requires input in program
  requires action == program[input]
  requires 0 <= at <= |s.1| - 2
  requires action.move == L
  requires s.1[at .. at + 2] == [TapeEnd, TapeHead(input.color, input.head)]
  ensures configStep(program, regularTapeConfig(s)).NextConfig?
  ensures
    var rewritten := performRewriteAt(s.1, MkRewriteRule([TapeEnd, TapeHead(input.color, input.head)], [TapeEnd, TapeHead(action.nextState, B0), TapeBit(action.write)]), at);
    regularTape(rewritten) &&
    regularTapeConfig((s.0-1, rewritten)) == configStep(program, regularTapeConfig(s)).nextConfig
{
  var rule := MkRewriteRule([TapeEnd, TapeHead(input.color, input.head)], [TapeEnd, TapeHead(action.nextState, B0), TapeBit(action.write)]);
  reveal singleHead();
  reveal elsewhereAreBits();
  assert rule.before[1..][0].TapeHead?;
  forall i | 0 <= i < |rule.before|-1 && i != 0 ensures rule.before[1..][i].TapeBit? {}
  assert singleHead(rule.before[1..]);
  assert rule.after[1..][0].TapeHead?;
  forall i | 0 <= i < |rule.after|-1 && i != 0 ensures rule.after[1..][i].TapeBit? {}
  assert singleHead(rule.after[1..]);
  assert singleHeadRule(rule);

  var rewritten := performRewriteAt(s.1, rule, at);
  singleHeadRulesPreservesRegularityAt(s.1, rule, at);
  assert regularTape(rewritten);

  var configBefore := regularTapeConfig(s);
  var configStepBefore := configStep(program, configBefore).nextConfig;
  var configAfter := regularTapeConfig((s.0-1, rewritten));
  assert configAfter.position == configStepBefore.position;
  assert configAfter.color == configStepBefore.color;

  assert at == 0;

  forall x ensures x in configAfter.tape <==> x in configStepBefore.tape {
    if x == configBefore.position {
      assert x in configStepBefore.tape <==> action.write == B1;
      assert x in configAfter.tape <==> 0 <= x - (s.0-1) < |rewritten| && bitIsOne(rewritten[x - (s.0-1)]);
      assert x - (s.0 - 1) == 2;
      assert rewritten[2] == rule.after[2];
      assert rule.after[2] == TapeBit(action.write);
      assert x in configAfter.tape <==> (action.write == B1);
      assert x in configAfter.tape <==> x in configStepBefore.tape;
    } else if x == configBefore.position - 1 {
      assert x - (s.0 - 1) == 1;
      assert x in configStepBefore.tape <==> x in configBefore.tape;
      assert x in configAfter.tape <==> rewritten[at+1] == TapeHead(action.nextState, B1);
      assert s.1[0] == TapeEnd;
      assert x in configAfter.tape <==> x in configStepBefore.tape;
    } else {
      assert x in configStepBefore.tape <==> x in configBefore.tape;
      assert x in configBefore.tape <==> (0 <= x-s.0 < |s.1| && s.1[x - s.0] == TapeBit(B1));
      assert x in configAfter.tape <==> 0 <= x - (s.0-1) < |rewritten| && bitIsOne(rewritten[x - (s.0-1)]);
      assert x in configAfter.tape <==> x in configStepBefore.tape;
    }
  }
  assert configAfter.tape == configStepBefore.tape;
  assert configAfter == configStepBefore;
}

function programRewriteRulesRightMiddle(program: Program): set<(int, Input, Action, RewriteRule)> {
  var bits := [B0, B1];
  (set input, b | b in bits && input in program && program[input].move == R :: var action := program[input]; (0, input, action, MkRewriteRule([TapeHead(input.color, input.head), TapeBit(b)], [TapeBit(action.write), TapeHead(action.nextState, b)])))
}

function programRewriteRulesRightEnd(program: Program): set<(int, Input, Action, RewriteRule)> {
  (set input | input in program && program[input].move == R :: var action := program[input]; (0, input, action, MkRewriteRule([TapeHead(input.color, input.head), TapeEnd], [TapeBit(action.write), TapeHead(action.nextState, B0), TapeEnd])))
}

function programRewriteRulesLeftMiddle(program: Program): set<(int, Input, Action, RewriteRule)> {
  var bits := [B0, B1];
  (set input, b | b in bits && input in program && program[input].move == L :: var action := program[input]; (0, input, action, MkRewriteRule([TapeBit(b), TapeHead(input.color, input.head)], [TapeHead(action.nextState, b), TapeBit(action.write)])))
}

function programRewriteRulesLeftEnd(program: Program): set<(int, Input, Action, RewriteRule)> {
  (set input | input in program && program[input].move == L :: var action := program[input]; (-1, input, action, MkRewriteRule([TapeEnd, TapeHead(input.color, input.head)], [TapeEnd, TapeHead(action.nextState, B0), TapeBit(action.write)])))
}

function {:opaque true} programRewriteRules(program: Program): set<(int, Input, Action, RewriteRule)> {
  programRewriteRulesRightMiddle(program)
  +
  programRewriteRulesRightEnd(program)
  +
  programRewriteRulesLeftMiddle(program)
  +
  programRewriteRulesLeftEnd(program)
}
lemma programRewriteRuleRightMiddle(program: Program, input: Input, action: Action, b: Bit)
  requires input in program
  requires action == program[input]
  requires action.move == R
  ensures (0, input, action, MkRewriteRule([TapeHead(input.color, input.head), TapeBit(b)], [TapeBit(action.write), TapeHead(action.nextState, b)])) in programRewriteRules(program)
{
  reveal programRewriteRules();
  assert b in [B0, B1];
}

lemma programRewriteRuleRightEnd(program: Program, input: Input, action: Action)
  requires input in program
  requires action == program[input]
  requires action.move == R
  ensures (0, input, action, MkRewriteRule([TapeHead(input.color, input.head), TapeEnd], [TapeBit(action.write), TapeHead(action.nextState, B0), TapeEnd])) in programRewriteRules(program)
{
  reveal programRewriteRules();
}

lemma programRewriteRuleLeftMiddle(program: Program, input: Input, action: Action, b: Bit)
  requires input in program
  requires action == program[input]
  requires action.move == L
  ensures (0, input, action, MkRewriteRule([TapeBit(b), TapeHead(input.color, input.head)], [TapeHead(action.nextState, b), TapeBit(action.write)])) in programRewriteRules(program)
{
  reveal programRewriteRules();
  assert b in [B0, B1];
}


lemma programRewriteRuleLeftEnd(program: Program, input: Input, action: Action)
  requires input in program
  requires action == program[input]
  requires action.move == L
  ensures (-1, input, action, MkRewriteRule([TapeEnd, TapeHead(input.color, input.head)], [TapeEnd, TapeHead(action.nextState, B0), TapeBit(action.write)])) in programRewriteRules(program)
{
  reveal programRewriteRules();
}


lemma programRewriteRulesAdvance(program: Program, tape: (int, TapeString), rule: (int, Input, Action, RewriteRule), at: int)
  requires regularTape(tape.1);
  requires rule in programRewriteRules(program)
  requires 0 <= at <= |tape.1| - |rule.3.before| && tape.1[at .. at + |rule.3.before|] == rule.3.before
  ensures configInput(regularTapeConfig(tape)) in program
  ensures regularTape(performRewriteAt(tape.1, rule.3, at))
  ensures regularTapeConfig((tape.0 + rule.0, performRewriteAt(tape.1, rule.3, at))) == configStep(program, regularTapeConfig(tape)).nextConfig
{
  var input := rule.1;
  var action := rule.2;
  var beforeConfig := regularTapeConfig(tape);
  reveal programRewriteRules();
  assert |rule.3.before| == 2;
  if rule.3.before[0].TapeHead? {
    assert action.move == R;
    // Moving right
    if rule.3.before[1].TapeBit? {
      // program: Program, input: Input, action: Action, s: (int, TapeString), at: nat, b: Bit
      rewriteRuleForMoveRightInto(program, input, action, tape, at, rule.3.before[1].tapeBit);
    } else {
      rewriteRuleForMoveRightEnd(program, input, action, tape, at);
    }
  } else {
    assert action.move == L;
    // Moving left
    if rule.3.before[0].TapeBit? {
      // program: Program, input: Input, action: Action, s: (int, TapeString), at: nat, b: Bit
      rewriteRuleForMoveLeftInto(program, input, action, tape, at, rule.3.before[0].tapeBit);
    } else {
      rewriteRuleForMoveLeftEnd(program, input, action, tape, at);
    }
  }
}


ghost predicate forwardClosedSet(program: Program, accepting: ((int, TapeString)) --> bool) {
  (forall t: (int, TapeString) | regularTape(t.1) :: accepting.requires(t))
  && regularTape(InitialTapeString.1)
  // We must accept the initial tape:
  && accepting(InitialTapeString)
  // If we accept a string, it must not be in a halting config:
  && (forall t: (int, TapeString) | regularTape(t.1) && accepting(t) :: configInput(regularTapeConfig(t)) in program)
                                                                        // If we accept a string, then after rewriting, we still accept it.
  && (forall t: (int, TapeString) | regularTape(t.1) && accepting(t) ::
    exists rule, at ::
      rule in programRewriteRules(program) && 0 <= at <= |t.1| - |rule.3.before|&&
      t.1[at .. at + |rule.3.before|] == rule.3.before &&
      var rewritten := performRewriteAt(t.1, rule.3, at);
      regularTape(rewritten) &&
      accepting((t.0 + rule.0, rewritten)))
}


lemma {:opaque true} closedStringSetImpliesLooping(program: Program, accepting: ((int, TapeString)) --> bool)
  requires forwardClosedSet(program, accepting)
  ensures programLoopsForever(program)
{
  forall n: nat ensures programConfigIter(program, n).NextConfig? {
    closedStringSetImpliesLoopingInduction(program, accepting, n);
  }
}

lemma {:opaque true} closedStringSetImpliesLoopingInduction(program: Program, accepting: ((int, TapeString)) --> bool, n: nat)
  requires forall t: (int, TapeString) | regularTape(t.1) :: accepting.requires(t)
  requires regularTape(InitialTapeString.1)
  // We must accept the initial tape:
  requires accepting(InitialTapeString)
  // If we accept a string, it must not be in a halting config:
  requires forall t: (int, TapeString) | regularTape(t.1) && accepting(t) :: configInput(regularTapeConfig(t)) in program
  // If we accept a string, then after rewriting, we still accept it.
  requires forall t: (int, TapeString) | regularTape(t.1) && accepting(t) ::
             exists rule, at ::
               rule in programRewriteRules(program) && 0 <= at <= |t.1| - |rule.3.before| &&
               t.1[at .. at + |rule.3.before|] == rule.3.before &&
               var rewritten := performRewriteAt(t.1, rule.3, at);
               regularTape(rewritten) &&
               accepting((t.0 + rule.0, rewritten))

  ensures programConfigIter(program, n).NextConfig?
  ensures exists f: (int, TapeString) :: regularTape(f.1) && regularTapeConfig(f) == programConfigIter(program, n).nextConfig && accepting(f)
{
  if n == 0 {
    initialTapeString();
    assert accepting(InitialTapeString);
    assert programConfigIter(program, n).NextConfig?;
    assert exists f: (int, TapeString) :: regularTape(f.1) && regularTapeConfig(f) == programConfigIter(program, n).nextConfig && accepting(f);
  } else {
    closedStringSetImpliesLoopingInduction(program, accepting, n-1);

    var prevF: (int, TapeString) :| regularTape(prevF.1) && regularTapeConfig(prevF) == programConfigIter(program, n-1).nextConfig && accepting(prevF);

    var rule, at :| rule in programRewriteRules(program) && 0 <= at <= |prevF.1| - |rule.3.before| &&
    prevF.1[at .. at + |rule.3.before|] == rule.3.before &&
    var rewritten := performRewriteAt(prevF.1, rule.3, at);
  regularTape(rewritten) &&
  accepting((prevF.0 + rule.0, rewritten));

    var nextF := performRewriteAt(prevF.1, rule.3, at);
    programRewriteRulesAdvance(program, prevF, rule, at);

    assert programConfigIter(program, n).NextConfig?;
    assert exists f: (int, TapeString) :: regularTape(f.1) && regularTapeConfig(f) == programConfigIter(program, n).nextConfig && accepting(f);
  }
}

ghost predicate isSinkAccept<V>(dfa: WholeDFA<V>, sinkAccept: V) {
  sinkAccept in dfa.follow && sinkAccept in dfa.accept && forall sym: TapeAlpha :: wholeDfaWorks(dfa, sinkAccept, sym); dfa.follow[sinkAccept][sym] == sinkAccept
}
ghost predicate isSinkReject<V>(dfa: WholeDFA<V>, sinkReject: V) {
  sinkReject in dfa.follow && sinkReject !in dfa.accept && forall sym: TapeAlpha :: wholeDfaWorks(dfa, sinkReject, sym); dfa.follow[sinkReject][sym] == sinkReject
}

function verifyPreservesRewriteProofTrigger<V>(v: V): int { 0 }

predicate {:opaque true} rewriteIntoPairs<V(!new)>(dfa: WholeDFA<V>, rule: RewriteRule, pairs: set<(V, V)>) {
  forall v | v in dfa.follow ::
  (followStringFrom(dfa, rule.before, v), followStringFrom(dfa, rule.after, v)) in pairs
}

lemma {:opaque true} rewriteIntoPairsInstance<V(!new)>(dfa: WholeDFA<V>, rule: RewriteRule, pairs: set<(V, V)>, v: V)
  requires v in dfa.follow
  requires rewriteIntoPairs(dfa, rule, pairs)
  ensures (followStringFrom(dfa, rule.before, v), followStringFrom(dfa, rule.after, v)) in pairs
{
  reveal rewriteIntoPairs();
}

lemma verifyPreservesRewriteProofHelper1<V(!new)>(dfa: WholeDFA<V>, rule: RewriteRule, pairs: set<(V, V)>, isOkay: bool)
  requires isOkay ==> funcForAll(dfa.vertexList, (v: V) requires v in dfa.vertexList => wholeDfaVertexEquivalence(dfa); (followStringFrom(dfa, rule.before, v), followStringFrom(dfa, rule.after, v)) in pairs)
  ensures isOkay ==> rewriteIntoPairs(dfa, rule, pairs)
{
  if isOkay {
    reveal funcForAll();
    reveal rewriteIntoPairs();
    forall v | v in dfa.follow ensures (followStringFrom(dfa, rule.before, v), followStringFrom(dfa, rule.after, v)) in pairs {
      wholeDfaVertexEquivalence(dfa);
      assert v in dfa.vertexList;
    }
  }
}

lemma {:opaque true} verifyPreservesRewriteProof<V(!new)>(dfa: WholeDFA<V>, rule: RewriteRule, initial: V, pairs: set<(V, V)>, isOkay: bool)
  requires initial in dfa.follow
  requires pairsInFollow(dfa, pairs)
  requires pairsAreSubsumed(dfa, pairs)
  requires isOkay ==> rewriteIntoPairs(dfa, rule, pairs)
  ensures
    isOkay ==>
      forall s, at | 0 <= at <= |s| - |rule.before| && s[at..at+|rule.before|] == rule.before && stringMatchesDFAFrom(dfa, s, initial) ::
        stringMatchesDFAFrom(dfa, performRewriteAt(s, rule, at), initial)
{
  if !isOkay {
    return;
  }
  wholeDfaVertexEquivalence(dfa);
  var vertexes := set v | v in dfa.follow;
  forall s, at | 0 <= at <= |s| - |rule.before| && s[at..at+|rule.before|] == rule.before && stringMatchesDFAFrom(dfa, s, initial)
    ensures stringMatchesDFAFrom(dfa, performRewriteAt(s, rule, at), initial)
  {
    var rewritten := performRewriteAt(s, rule, at);
    stringMatchesDFAFromEventually(dfa, s, initial, at);
    stringMatchesDFAFromEventually(dfa, rewritten, initial, at);
    // At some point, just before the rewrite rule, we end at this vertex:
    var lastCommonVertex := followStringFrom(dfa, s[..at], initial);
    assert rewritten[..at] == s[..at];

    // We know that following lastCommonVertex, we are accepted before:
    assert stringMatchesDFAFrom(dfa, s[at..], lastCommonVertex);
    // So we want to prove that following lastCommonVertex, we are accepted after the rewrite:
    assert stringMatchesDFAFrom(dfa, rewritten[at..], lastCommonVertex) ==> stringMatchesDFAFrom(dfa, rewritten, initial);

    var tailBefore := s[at..];
    var tailAfter := rewritten[at..];
    assert tailBefore[..|rule.before|] == rule.before;
    assert tailAfter[..|rule.after|] == rule.after;

    assert tailBefore[|rule.before|..] == tailAfter[|rule.after|..];
    var commonEnd := tailBefore[|rule.before|..];

    stringMatchesDFAFromEventually(dfa, tailBefore, lastCommonVertex, |rule.before|);
    assert stringMatchesDFAFrom(dfa, tailBefore, lastCommonVertex) <==> stringMatchesDFAFrom(dfa, commonEnd, followStringFrom(dfa, rule.before, lastCommonVertex));

    assert tailAfter[..|rule.after|] == rule.after;
    stringMatchesDFAFromEventually(dfa, tailAfter, lastCommonVertex, |rule.after|);
    assert stringMatchesDFAFrom(dfa, tailAfter, lastCommonVertex) <==> stringMatchesDFAFrom(dfa, commonEnd, followStringFrom(dfa, rule.after, lastCommonVertex));

    var vertexThenBefore := followStringFrom(dfa, rule.before, lastCommonVertex);
    var vertexThenAfter := followStringFrom(dfa, rule.after, lastCommonVertex);
    assert lastCommonVertex in vertexes;
    assert verifyPreservesRewriteProofTrigger(lastCommonVertex) == 0;
    rewriteIntoPairsInstance(dfa, rule, pairs, lastCommonVertex);
    assert (vertexThenBefore, vertexThenAfter) in pairs;


    reveal pairsAreSubsumed();
    assert stringMatchesDFAFrom(dfa, tailBefore[|rule.before|..], vertexThenBefore);
    reveal vertexSubsumption();

    assert stringMatchesDFAFrom(dfa, rewritten[at..], lastCommonVertex);
  }
}

function verifyPreservesRewriteTrigger(s: TapeString, at: int): int { 0 }

function {:opaque true} verifyPreservesRewrite<V(!new, ==)>(dfa: WholeDFA<V>, rule: RewriteRule, initial: V, pairs: set<(V, V)>): (isOkay: bool)
  requires initial in dfa.follow
  requires pairsInFollow(dfa, pairs)
  requires pairsAreSubsumed(dfa, pairs)
  ensures isOkay ==> forall s, at {:trigger verifyPreservesRewriteTrigger(s, at)} | 0 <= at <= |s| - |rule.before| && s[at..at+|rule.before|] == rule.before && stringMatchesDFAFrom(dfa, s, initial) :: stringMatchesDFAFrom(dfa, performRewriteAt(s, rule, at), initial)
{

  wholeDfaVertexEquivalence(dfa);
  var checked := checkAllRecursive(dfa.vertexList, (v: V) requires v in dfa.vertexList =>
  (followStringFrom(dfa, rule.before, v), followStringFrom(dfa, rule.after, v)) in pairs
  );
  assert checked ==>
      funcForAll(dfa.vertexList, (v: V) requires v in dfa.vertexList => (followStringFrom(dfa, rule.before, v), followStringFrom(dfa, rule.after, v)) in pairs)
    ;
  verifyPreservesRewriteProofHelper1(dfa, rule, pairs, checked);
  verifyPreservesRewriteProof(dfa, rule, initial, pairs, checked);
  checked
}

method verifyStrictDfaPropertiesForProgram<V(!new, ==)>(program: Program, dfa: WholeDFA<V>, initialVertex: V, sinkAccept: V, sinkReject: V) returns (isOkay: bool)
  requires initialVertex in dfa.follow
  ensures isOkay ==> programLoopsForever(program)
{
  var allInputs := set b, c | b in [B0, B1] && c in [CA, CB, CC, CD, CE] :: Input(b, c);
  forall input: Input ensures input in allInputs {
    assert input.color == CA || input.color == CB || input.color == CC || input.color == CD || input.color == CE;
    assert input.head == B0 || input.head == B1;
  }

  var allSymbols := methodAllTapeAlpha();
  methodAllTapeAlphaWorks();

  if sinkAccept !in dfa.follow || sinkReject !in dfa.follow {
    return false;
  }
  if sinkAccept !in dfa.accept || sinkReject in dfa.accept {
    return false;
  }

  var isSinkAcceptOkay := checkAll(allSymbols, sym => wholeDfaWorks(dfa, sinkAccept, sym); dfa.follow[sinkAccept][sym] == sinkAccept);
  if !isSinkAcceptOkay {
    return false;
  }

  var isSinkRejectOkay := checkAll(allSymbols, sym => wholeDfaWorks(dfa, sinkReject, sym); dfa.follow[sinkReject][sym] == sinkReject);
  if !isSinkRejectOkay {
    return false;
  }

  var accepting := (s: (int, TapeString)) requires regularTape(s.1) => stringMatchesDFAFrom(dfa, s.1, initialVertex);

  // Initial state matches:
  assert (forall t: (int, TapeString) | regularTape(t.1) :: accepting.requires(t));
  initialTapeString();
  assert regularTape(InitialTapeString.1);
  wholeDfaWorks(dfa, initialVertex, TapeEnd);
  var vInitialTapeEnd := dfa.follow[initialVertex][TapeEnd];
  assert stringMatchesDFAFrom(dfa, InitialTapeString.1, initialVertex) <==> stringMatchesDFAFrom(dfa, InitialTapeString.1[1..], vInitialTapeEnd);
  wholeDfaWorks(dfa, vInitialTapeEnd, TapeHead(CA, B0));
  var vInitialTapeEndAlpha := dfa.follow[vInitialTapeEnd][TapeHead(CA, B0)];
  assert stringMatchesDFAFrom(dfa, InitialTapeString.1, initialVertex) <==> stringMatchesDFAFrom(dfa, InitialTapeString.1[2..], vInitialTapeEndAlpha);
  wholeDfaWorks(dfa, vInitialTapeEndAlpha, TapeEnd);
  var vInitialTapeStringEnd := dfa.follow[vInitialTapeEndAlpha][TapeEnd];
  assert stringMatchesDFAFrom(dfa, InitialTapeString.1, initialVertex) <==> stringMatchesDFAFrom(dfa, InitialTapeString.1[3..], vInitialTapeStringEnd);
  if vInitialTapeStringEnd !in dfa.accept {
    return false;
  }
  assert stringMatchesDFAFrom(dfa, InitialTapeString.1, initialVertex);
  assert accepting(InitialTapeString);

  // Halting states are not accepted:

  var haltingInputs := set input: Input | input in allInputs && input !in program :: input;
  var haltingInputPairs := set input: Input, v: V | input in haltingInputs && v in dfa.follow :: (input, v);
  var haltingInputOkay := checkAll(haltingInputPairs, (p: (Input, V)) requires p.1 in dfa.follow =>
                                     var input := p.0;
                                     var v := p.1;
                                     var inputSym := TapeHead(input.color, input.head);
                                     wholeDfaWorks(dfa, v, inputSym);
                                     dfa.follow[v][inputSym] == sinkReject
  );
  if !haltingInputOkay {
    return false;
  }

  forall alpha: TapeAlpha, v: V | alpha.TapeHead? && Input(alpha.tapeHeadBit, alpha.tapeHeadState) in haltingInputs && v in dfa.follow
    ensures alpha in dfa.follow[v] && dfa.follow[v][alpha] == sinkReject {
    wholeDfaWorks(dfa, v, alpha);
    assert (Input(alpha.tapeHeadBit, alpha.tapeHeadState), v) in haltingInputPairs;
  }

  forall t: (int, TapeString) | regularTape(t.1) && configInput(regularTapeConfig(t)) !in program ensures !accepting(t) {
    var c := regularTapeConfig(t);
    assert configInput(c) !in program;
    var headIndex :| 0 <= headIndex < |t.1| && t.1[headIndex].TapeHead?;
    assert configInput(c) == Input(t.1[headIndex].tapeHeadBit, t.1[headIndex].tapeHeadState);
    stringMatchesDFAFromEventually(dfa, t.1, initialVertex, headIndex);
    var vBeforeHead :| vBeforeHead in dfa.follow && (stringMatchesDFAFrom(dfa, t.1, initialVertex) <==> stringMatchesDFAFrom(dfa, t.1[headIndex..], vBeforeHead));
    wholeDfaWorks(dfa, vBeforeHead, t.1[headIndex]);
    assert configInput(c) in haltingInputs;
    assert dfa.follow[vBeforeHead][t.1[headIndex]] == sinkReject;
  }

  forall t: (int, TapeString) | regularTape(t.1) && accepting(t) ensures configInput(regularTapeConfig(t)) in program {
    // Immediate corrolary by contrapositive.
  }

  var programRewrites := programRewriteRules(program);

  // First, we prove that all accepted tapes are non-halting, so they have a rewrite rule:
  forall t: (int, TapeString) | regularTape(t.1) && accepting(t) ensures
      exists rule, at :: rule in programRewrites && 0 <= at <= |t.1| - |rule.3.before|&&
                         t.1[at .. at + |rule.3.before|] == rule.3.before
  {
    var tape := t.1;
    var i :| 1 <= i < |tape|-1 && tape[i].TapeHead? &&
      forall j | (1 <= j < |tape|-1 && j != i) :: tape[j].TapeBit?;
    var c := regularTapeConfig(t);
    var input := configInput(c);
    assert input in program;
    var action := program[input];
    if action.move == R {
      if i != |tape| - 2 {
        assert tape[i+1].TapeBit?;
        var b := tape[i+1].tapeBit;
        assert input in program;
        var ruleMiddle := (0, input, action, MkRewriteRule([TapeHead(input.color, input.head), TapeBit(b)], [TapeBit(action.write), TapeHead(action.nextState, b)]));
        assert b in [B0, B1];
        programRewriteRuleRightMiddle(program, input, action, b);
        assert ruleMiddle in programRewrites;
        assert 0 <= i <= |tape| - |ruleMiddle.3.before|;
        assert |ruleMiddle.3.before| == 2;
        assert tape[i] == ruleMiddle.3.before[0];
        assert tape[i+1] == ruleMiddle.3.before[1];
        assert tape[i .. i + |ruleMiddle.3.before|] == ruleMiddle.3.before;

        assert exists rule, at :: rule in programRewrites && 0 <= at <= |t.1| - |rule.3.before|&&
                                  t.1[at .. at + |rule.3.before|] == rule.3.before;
      } else {
        var ruleEnd := (0, input, action, MkRewriteRule([TapeHead(input.color, input.head), TapeEnd], [TapeBit(action.write), TapeHead(action.nextState, B0), TapeEnd]));
        assert tape[i+1].TapeEnd?;
        assert input in program;
        programRewriteRuleRightEnd(program, input, action);
        assert ruleEnd in programRewrites;
        assert |ruleEnd.3.before| == 2;
        assert tape[i] == ruleEnd.3.before[0];
        assert tape[i+1] == ruleEnd.3.before[1];
        assert tape[i .. i + |ruleEnd.3.before|] == ruleEnd.3.before;

        assert exists rule, at :: rule in programRewrites && 0 <= at <= |t.1| - |rule.3.before|&&
                                  t.1[at .. at + |rule.3.before|] == rule.3.before;
      }
    } else {
      if i != 1 {
        assert tape[i-1].TapeBit?;
        var b := tape[i-1].tapeBit;
        assert input in program;
        var ruleMiddle := (0, input, action, MkRewriteRule([TapeBit(b), TapeHead(input.color, input.head)], [TapeHead(action.nextState, b), TapeBit(action.write)]));
        assert b in [B0, B1];
        programRewriteRuleLeftMiddle(program, input, action, b);
        assert ruleMiddle in programRewrites;
        assert 0 <= i-1 <= |tape| - |ruleMiddle.3.before|;
        assert |ruleMiddle.3.before| == 2;

        var iBegin := i-1;
        assert 0 <= iBegin <= |t.1| - |ruleMiddle.3.before|;
        assert tape[iBegin] == ruleMiddle.3.before[0];
        assert tape[iBegin+1] == ruleMiddle.3.before[1];
        var slice := tape[iBegin .. iBegin + |ruleMiddle.3.before|];
        assert |slice| == 2 == |ruleMiddle.3.before|;
        assert slice[0] == ruleMiddle.3.before[0];
        assert slice[1] == ruleMiddle.3.before[1];
        assert tape[iBegin .. iBegin + |ruleMiddle.3.before|] == ruleMiddle.3.before;
        assert 0 <= iBegin <= |tape| - |ruleMiddle.3.before|;

        assert exists rule, at :: rule in programRewrites && 0 <= at <= |t.1| - |rule.3.before| &&
                                  t.1[at .. at + |rule.3.before|] == rule.3.before;
      } else {
        var ruleEnd := (-1, input, action, MkRewriteRule([TapeEnd, TapeHead(input.color, input.head)], [TapeEnd, TapeHead(action.nextState, B0), TapeBit(action.write)]));
        assert tape[i-1].TapeEnd?;
        assert input in program;
        programRewriteRuleLeftEnd(program, input, action);
        assert ruleEnd in programRewrites;
        assert |ruleEnd.3.before| == 2;
        var iBegin := i-1;
        assert 0 <= iBegin <= |t.1| - |ruleEnd.3.before|;
        assert tape[iBegin] == ruleEnd.3.before[0];
        assert tape[iBegin+1] == ruleEnd.3.before[1];
        assert tape[iBegin .. iBegin + |ruleEnd.3.before|] == ruleEnd.3.before;

        assert exists rule, at :: rule in programRewrites && 0 <= at <= |t.1| - |rule.3.before|&&
                                  t.1[at .. at + |rule.3.before|] == rule.3.before;
      }
    }
  }

  var subsumptionPairs := computeDfaAcceptanceSubsets(dfa);

  var allRuleRewritesOkay := checkAll(programRewrites, rule requires rule in programRewrites =>
                                        verifyPreservesRewrite(dfa, rule.3, initialVertex, subsumptionPairs)
  );
  if !allRuleRewritesOkay {
    return false;
  }

  forall t: (int, TapeString) | regularTape(t.1) && accepting(t) ensures
      exists rule, at ::
        rule in programRewriteRules(program) && 0 <= at <= |t.1| - |rule.3.before| &&
        t.1[at .. at + |rule.3.before|] == rule.3.before &&
        var rewritten := performRewriteAt(t.1, rule.3, at);
        regularTape(rewritten) &&
        accepting((t.0 + rule.0, rewritten))
  {
    var rule, at :| rule in programRewriteRules(program) && 0 <= at <= |t.1| - |rule.3.before| && t.1[at .. at + |rule.3.before|] == rule.3.before;
    var rewritten := performRewriteAt(t.1, rule.3, at);
    programRewriteRulesAdvance(program, t, rule, at); // If we use this rule, we get a regular string.
    assert regularTape(rewritten);
    assert verifyPreservesRewriteTrigger(t.1, at) == 0;
    assert stringMatchesDFAFrom(dfa, rewritten, initialVertex);
    assert accepting((t.0 + rule.0, rewritten));
  }

  assert forwardClosedSet(program, accepting);
  closedStringSetImpliesLooping(program, accepting);
  return true;
}

method checkWholeDfaFollowForward<V(!new, ==)>(dfa: DFA<V>) returns (isOkay: bool)
  ensures isOkay ==> (forall v | v in dfa.follow :: forall x :: x in dfa.follow[v] && dfa.follow[v][x] in dfa.follow)
{
  var allAlpha := methodAllTapeAlpha();
  methodAllTapeAlphaWorks();

  var remaining: set<V> := dfa.follow.Keys;
  while remaining != {}
    invariant remaining <= dfa.follow.Keys
    invariant forall v | v in dfa.follow && v !in remaining :: forall x :: x in dfa.follow[v] && dfa.follow[v][x] in dfa.follow
  {
    var v :| v in remaining;

    var isAllAlphaIn := checkAll(allAlpha, x => x in dfa.follow[v]);
    if !isAllAlphaIn {
      return false;
    }
    assert forall x: TapeAlpha :: x in allAlpha;
    assert forall x: TapeAlpha :: x in allAlpha ==> x in dfa.follow[v];
    assert forall x: TapeAlpha :: x in dfa.follow[v];

    var nextAllIn := checkAll(allAlpha, x => dfa.follow[v][x] in dfa.follow);
    if !nextAllIn {
      return false;
    }

    assert forall x: TapeAlpha :: x in allAlpha ==> dfa.follow[v][x] in dfa.follow;
    assert forall x :: x in dfa.follow[v] && dfa.follow[v][x] in dfa.follow;
    remaining := remaining - {v};
  }
  return true;
}

method checkWholeDfaVertexList<V(!new, ==)>(dfa: DFA<V>) returns (isOkay: bool)
  ensures isOkay ==> (forall v | v in dfa.follow :: v in dfa.follow <==> v in dfa.vertexList)
{
  var followSet := dfa.follow.Keys;
  var eachIn := checkAll(followSet, v => v in dfa.follow <==> v in dfa.vertexList);
  if !eachIn {
    return false;
  }
  assert forall v | v in dfa.follow :: v in dfa.follow <==> v in dfa.vertexList;
  return true;
}

method checkWholeDfaFollowList<V(!new, ==)>(dfa: DFA<V>) returns (isOkay: bool)
  ensures isOkay ==> (forall v | v in dfa.vertexList :: v in dfa.follow <==> v in dfa.vertexList)
{
  var followSet := dfa.follow.Keys;
  var eachIn := checkAllRecursive(dfa.vertexList, v => v in dfa.follow <==> v in dfa.vertexList);
  if !eachIn {
    return false;
  }
  reveal funcForAll();
  assert forall v | v in dfa.vertexList :: v in dfa.follow <==> v in dfa.vertexList;
  return true;
}

method verifyDfaPropertiesForProgram<V(!new, ==)>(program: Program, dfa: DFA<V>, initialVertex: V, sinkAccept: V, sinkReject: V) returns (isOkay: bool)
  ensures isOkay ==> programLoopsForever(program)
{
  if initialVertex !in dfa.follow {
    return false;
  }
  reveal wholeDfa();
  var isOkay1 := checkWholeDfaFollowForward(dfa);
  if !isOkay1 {
    return false;
  }
  var isOkay2 := checkWholeDfaVertexList(dfa);
  if !isOkay2 {
    return false;
  }
  var isOkay3 := checkWholeDfaFollowList(dfa);
  if !isOkay3 {
    return false;
  }
  assert wholeDfa(dfa);
  isOkay := verifyStrictDfaPropertiesForProgram(program, dfa, initialVertex, sinkAccept, sinkReject);
}