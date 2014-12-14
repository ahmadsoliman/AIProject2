import itertools
from copy import *
from unifier import *

counter = 0

class action:
    def __init__(self, name, preconds, effects):
        self.name = name
        self.preconds = preconds
        self.effects = effects
    def __repr__(self):
        return self.name.__repr__()
    def __eq__(self, other):
        ret = self.name.eq(other.name) and\
                arrayEq(sorted(self.preconds), sorted(other.preconds)) and\
                arrayEq(sorted(self.effects), sorted(other.effects))
        return ret
    def __ne__(self, other):
        return not(self.eq(other))
    #def __hash__(self):
    #    return self.__repr__().__hash__()
    def clone(self, fresh=True):
        dic = {}
        def assignVar(vname):
            global counter
            if vname not in dic:
                counter += 1
                dic[vname] = "X%s" % counter
            return dic[vname]
        def replaceNames(node):
            if not fresh: return node
            if node.kind == 'var':
                node.name = assignVar(node.name)
            else:
                for c in node.children:
                    replaceNames(c)
            return node

        newname = replaceNames(self.name.clone())
        newpreconds = [replaceNames(p.clone()) for p in self.preconds]
        neweffects = [replaceNames(e.clone()) for e in self.effects]
        return action(newname, newpreconds, neweffects)

def arrayEq(a1, a2):
    if len(a1)!=len(a2):
        return False
    for b1,b2 in itertools.izip(a1,a2):
        if not unify(b1, b2).found: return False
    return True


def inArray(action, actions, sol):
    action = action.clone(False)
    action.preconds = [subst(sol, precond) for precond in action.preconds]
    action.effects = [subst(sol, effect) for effect in action.effects]
    newactions = []
    for action1 in actions:
        action1 = action1.clone(False)
        action1.preconds = [subst(sol, precond) for precond in action1.preconds]
        action1.effects = [subst(sol, effect) for effect in action1.effects]
        newactions.append(action1)
    return action in newactions

# operations O is an array of actions
ops = []
a0 = None
aInf = None

def POP(O, s0, g):
    global ops, a0, aInf
    a0 = action(const('start'), [], s0)
    aInf = action(const('finish'), g, [])
    ops.append(a0)
    ops.append(aInf)
    ops += O
    agenda = []
    for precond in g:
        agenda.append((aInf, precond))
    return POP1(([a0, aInf], [], [(a0, aInf)], solution(True)), agenda)

# pi is a 4-tuple <A,L,Ord,B>

def POP1(PI, agenda):
    # if counter > 20:
    #     exit(0)

    A, L, Ord, B = PI
    # expand pi tuple
    #print 'A: ', A
    # print 'L: ', L
    # print 'Ord: ', Ord
    # print 'B: ', B
    #print 'agenda: ', agenda

    # if (agenda = phi) then return pi
    if len(agenda) == 0:
        return PI
    # Select any pair (ai, pi) and remove it from agenda
    ai, pi = agenda.pop()
    # achievers = the set of operators achieving (ai, pi)
    # nondeterminsticly choose operator aj from achievers
    for op in ops:
        op = op.clone()
        for effect in op.effects:
            if effect.sameFn(pi):
                A, L, Ord, B = PI
                A = [a.clone(False) for a in A]
                L = [(l[0].clone(False), l[1].clone(), l[2].clone(False)) for l in L]
                Ord = [(l[0].clone(False), l[1].clone(False)) for l in Ord]
                B = B.clone()
                PI = (A, L, Ord, B)

                aj = op
                #print 'aj: : : : : : : :: : ', aj
                sol = unify(effect, pi)
                # if achievers = [] return failure
                if aj is None:
                    return None

                # L = L union { aj --pi--> ai }
                L.append((aj, pi, ai))
                # update Ord with aj < ai
                if (aj, ai) not in Ord:
                    Ord.append((aj, ai))

                # Update B with binding constraints of this link
                if not B.consistent(sol):
                    continue
                B.merge(sol)

                if not inArray(aj, A, B):
                    # A = A union {aj}
                    A.append(aj)
                    # update Ord with a0 < aj and aj < aInf
                    if not(a0.name==aj.name):
                        if (a0, ai) not in Ord:
                            Ord.append((a0, aj))
                    if not(aj.name==aInf.name):
                        if (aj, aInf) not in Ord:
                            Ord.append((aj, aInf))
                    # add all preconditions of aj to the agenda
                    for precond in aj.preconds:
                        agenda.append((aj, precond))
                # resolve new threats
                #PI = RESOLVE_THREATS((A, L, Ord, B), aj, (aj, pi, ai))
                resPI = POP1((A, L, Ord, B), agenda)
                if resPI is not None: return resPI

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
                        Ord1 = [(l[0].clone(False), l[1].clone(False)) for l in Ord]
                        if (ai, ak) not in Ord:
                            Ord1.append((ai, ak))
                        if (ak, aj) not in Ord:
                            Ord1.append((ak, aj))
                        if not consistentOrder(Ord1):
                            sol = None
                            continue
                        break
                if sol:
                    if (ak, ai) not in Ord:
                        Ord.append((ak, ai))
    return (A, L, Ord, B)

def consistentOrder(pairs):
    nodec = 0
    nodem = []
    for a,b in pairs:
        if a not in nodem:
            nodem.append(a)
        if b not in nodem:
            nodem.append(b)
    graph = [[]]*len(nodem)
    for a,b in pairs:
        x=nodem.index(a)
        y=nodem.index(b)
        if y not in graph[x]: graph[x].append(y)
        if x not in graph[y]: graph[y].append(x)
    return dfs(graph, set([]), 0, -1)

def dfs(graph, vis, n, p):
    if n in vis:
        return False
    vis.add(n)
    for adj in graph[n]:
        if adj != p:
            if not dfs(graph, vis, adj, n):
                return False
    return True


def linearize(pairs, sol):
    nodec = 0
    nodem = []
    for a,b in pairs:
        if a.name not in nodem:
            nodem.append(a.name)
        if b.name not in nodem:
            nodem.append(b.name)
    graph = [[]]*len(nodem)
    for a,b in pairs:
        x=nodem.index(a.name)
        y=nodem.index(b.name)
        if y not in graph[x]: graph[x].append(y)
        if x not in graph[y]: graph[y].append(x)
    global a0
    res = []
    top_sort(graph, set([]), nodem.index(a0.name), res)
    items = []
    res = reversed(res)
    for item in res:
        nodem[item] = subst(sol, nodem[item])
        nodem[item] = subst(sol, nodem[item])
        nodem[item] = subst(sol, nodem[item])
        items.append(nodem[item])
    return items

def top_sort(graph, vis, node, res):
    vis.add(node)
    for adj in graph[node]:
        if not adj in vis:
            top_sort(graph, vis, adj, res)
    res.append(node)

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
    action(fn('Buy', var('Store'), var('Y')),
            [fn('At', var('Store')), fn('Sells', var('Store'), var('Y'))],
            [fn('Have', var('Y'))]
        )
]

plan = POP(O, s0, g)

print plan

print linearize(plan[2], plan[3])
