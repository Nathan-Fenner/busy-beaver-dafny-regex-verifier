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

function method offsetOfDirection(d: Direction): int {
  if d == R then 1 else -1
}

// An action describes what the machine might be told to do by a program:
// - write the given bit
// - switch to the given color
// - move one step in given direction
datatype Action = Action(write: Bit, nextState: State, move: Direction)

// configStepAction applies the given action to the machine state.
function method configStepAction(m: MachineConfig, action: Action): MachineConfig {
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

function method configInput(c: MachineConfig): Input {
  Input(if c.position in c.tape then B1 else B0, c.color)
}

// configStep causes the provided state to step forward once according to the
// provided program. The output will either be the next state, or Halt if there
// is no configured transition.
function method configStep(program: Program, c: MachineConfig): MachineStep {
  var input := configInput(c);
  if input in program
    then NextConfig(configStepAction(c, program[input]))
    else Halt
}

// This function is a helper for moving 'n' steps forward in time.
// It is a `function` rather than `function method` because it will cause stack-overflow if run
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
predicate programEventuallyHalts(program: Program) {
  exists n :: n >= 0 && programConfigIter(program, n).Halt?
}

// A program loops forever if it never halts.
predicate programLoopsForever(program: Program) {
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

function method stateFromChar(s: char): State {
  match s {
    case 'A' => CA
    case 'B' => CB
    case 'C' => CC
    case 'D' => CD
    case 'E' => CE
    case _ => CA // Avoid
  }
}

function method bitFromChar(s: char): Bit {
  match s {
    case '0' => B0
    case '1' => B1
    case _ => B0 // Avoid
  }
}

function method dirFromChar(s: char): Direction {
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

function regularTapeConfig(str: seq<TapeAlpha>): MachineConfig
requires regularTape(str) {
  var i :| 1 <= i < |str|-1 && str[i].TapeHead?;
  MachineConfig(
    position := i,
    color := str[i].tapeHeadState,
    tape := set j | 0 <= j < |str| && bitIsOne(str[j]) :: j
  )
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

function singleHeadIndex(tape: TapeString): (r: nat)
requires singleHead(tape)
ensures 0 <= r < |tape|
ensures tape[r].TapeHead? && elsewhereAreBits(tape, r)
{
  reveal singleHead();
  var out :| 0 <= out < |tape| && tape[out].TapeHead?;
  singleHeadIndexWorks(tape, out);
  out
}

predicate singleHeadRule(rule: RewriteRule) {
  singleHead(rule.before) && singleHead(rule.after)
}

lemma singleHeadRulesPreservesRegularityAt(tape: TapeString, rule: RewriteRule, at: nat)
requires regularTape(tape)
requires singleHeadRule(rule)
requires 0 <= at <= |tape| - |rule.before|
requires |rule.before| > 0
requires tape[at .. at + |rule.before|] == rule.before
ensures regularTape(performRewriteAt(tape, rule, at))
{
  reveal singleHead();
  reveal elsewhereAreBits();

  var rewritten := performRewriteAt(tape, rule, at);
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
  accept: set<Vertex>
)

predicate {:opaque true} wholeDfa<Vertex>(dfa: DFA<Vertex>) {
forall v | v in dfa.follow :: forall x :: x in dfa.follow[v] && dfa.follow[v][x] in dfa.follow
}

lemma wholeDfaWorks<V>(d: WholeDFA<V>, a: V, x: TapeAlpha) requires a in d.follow ensures x in d.follow[a] && d.follow[a][x] in d.follow {
  reveal wholeDfa();
}

type WholeDFA<Vertex> = dfa: DFA | wholeDfa(dfa) witness *

function followStringFrom<Vertex>(d: WholeDFA<Vertex>, tape: TapeString, from: Vertex): Vertex
requires from in d.follow {
  if |tape| == 0 then from else
  reveal wholeDfa();
  followStringFrom(d, tape[1..], d.follow[from][tape[0]])
}

predicate stringMatchesDFAFrom<Vertex>(d: WholeDFA<Vertex>, tape: TapeString, from: Vertex)
requires from in d.follow
{
  followStringFrom(d, tape, from) in d.accept
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

predicate {:opaque} vertexSubsumption<Vertex>(d: WholeDFA<Vertex>, a: Vertex, b: Vertex)
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

predicate {:opaque true} pairsInNext<V(!new)>(d: WholeDFA<V>, pairs: set<(V, V)>)
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

function method {:opaque true} dfaAcceptedSubsetExcludeTerminal<V(!new)>(pairs: set<(V, V)>, accept: set<V>): (newExclude: set<(V, V)>)
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

function method methodAllTapeAlpha(): (r: set<TapeAlpha>)
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

function method {:opaque true} dfaAcceptedSubsetExcludeChainedBit<V(!new)>(pairs: set<(V, V)>, d: WholeDFA<V>): (newExclude: set<(V, V)>)
requires pairsInFollow(d, pairs)
ensures newExclude <= pairs
// ensures forall p, x | p in pairs && x in d.follow[p.0] && x in d.follow[p.1] && (d.follow[p.0][x], d.follow[p.1][x]) !in pairs :: p in newExclude 
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

predicate {:opaque true} pairsAreSubsumed<V>(d: WholeDFA<V>, pairs: set<(V, V)>)
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

