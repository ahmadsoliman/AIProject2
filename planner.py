import itertools
from copy import *
from unifier import *

class action:
    def __init__(self, name, preconds, effects):
        self.name = name
        self.preconds = preconds
        self.effects = effects
    def __repr__(self):
        return self.name.__repr__()
    def __eq__(self, other):
        return self.name == other.name and self.preconds == other.preconds and self.effects == other.preconds
    def __hash__(self):
        return id(self)

# operations O is an array of actions
ops = []
a0 = None
aInf = None

def POP(O, s0, g):
    global ops, a0, aInf
    ops = O
    a0 = action(const('start'), [], s0)
    aInf = action(const('finish'), g, [])
    ops.append(a0)
    ops.append(aInf)
    agenda = []
    for precond in g:
        agenda.append((aInf, precond))
    return POP1(([a0, aInf], [], set([(a0, aInf)]), solution(True)), agenda)

# pi is a 4-tuple <A,L,Ord,B>

def POP1(PI, agenda):
    # expand pi tuple
    A, L, Ord, B = PI
    print 'A: ', A
    print 'L: ', L
    print 'Ord: ', Ord
    print 'B: ', B
    print 'agenda: ', agenda

    # if (agenda = phi) then return pi
    if len(agenda) == 0:
        return PI
    # Select any pair (ai, pi) and remove it from agenda
    ai, pi = agenda.pop()
    # achievers = the set of operators achieving (ai, pi)
    # nondeterminsticly choose operator aj from achievers
    aj = None
    sol = None
    found = False
    for op in ops:
        if found:
            break
        for effect in op.effects:
            if effect.sameFn(pi):
                aj = op
                sol = unify(effect, pi)
                found = True
                break
    # if achievers = [] return failure
    if aj is None:
        return None
    # subst(sol, aj)
    aj.name = subst(sol, aj.name)
    for precond in aj.preconds:
        subst(sol, precond)
    for effect in aj.effects:
        subst(sol, effect)

    # L = L union { aj --pi--> ai }
    L.append((aj, pi, ai))
    # update Ord with aj < ai
    Ord.add((aj, ai))
    # Update B with binding constraints of this link
    B.merge(sol)

    if not(aj in A):
        # A = A union {aj}
        A.append(aj)
        # update Ord with a0 < aj and aj < aInf
        Ord.add((a0, aj))
        Ord.add((aj, aInf))
        # add all preconditions of aj to the agenda
        for precond in aj.preconds:
            agenda.append((aj, precond))
    # resolve new threats
    #PI = RESOLVE_THREATS((A, L, Ord, B), aj, (aj, pi, ai))
    return POP1(PI, agenda)

def RESOLVE_THREATS(PI, al, l):
    # expand pi tuple
    A, L, Ord, B = PI
    for ak in A:
        for ai, pij, aj in L:
            if ak==al or (ai, pij, aj)==l:
                sol = None
                for effect in ak.effects:
                    if effect.isNotOf(pij):
                        sol = unify(effect.posOf(), pij.posOf())
                        if not sol.consistent(B):
                            sol = None
                            continue
                        Ord1 = copy(Ord)
                        Ord1.add((ai, ak))
                        Ord1.add((ak, aj))
                        if not consistentOrder(Ord1):
                            sol = None
                            continue
                        break
                if sol:
                    Ord.add((ak, ai))
    return (A, L, Ord, B)

def consistentOrder(pairs):
    return True




# test

s0 = [
    fn('At', const('home')),
    fn('Sells', const('hws'), const('drill')),
    fn('Sells', const('sm'), const('milk')),
    fn('Sells', const('sm'), const('banana'))
]

g = [
    fn('At', const('home')),
    fn('Have', const('drill')),
    fn('Have', const('milk')),
    fn('Have', const('banana'))
]

O = [
    action(fn('Go', var('Here'), var('There')),
            [fn('At', var('Here'))],
            [fn('At', var('There')), neg(fn('At', var('Here')))]
        ),
    action(fn('Buy', var('Store'), var('X')),
            [fn('At', var('Store')), fn('Sells', var('Store'), var('X'))],
            [fn('Have', var('X'))]
        )
]

print POP(O, s0, g)
