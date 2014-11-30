import itertools
from clause import *

'''
class Function:
    ATOM = 0
    VAR = 1
    FUNC = 2
    def __init__(self, name, ftype, args=[]):
        self.name = name
        self.type = ftype
        self.args = args

    def eq(self, other):
        if self.type != other.type or self.name != other.name:
            return False
        for arg1,arg2 in itertools.izip(self.args, other.args):
            if not(arg1.eq(arg2)):
                return False
        return True

    def humanize(self):
        if self.type == Function.ATOM or self.type == Function.VAR:
            return self.name
        res = self.name + '('
        for arg in self.args:
            res += humanize(arg) + ','
        return res[:-1] + ')'
'''

class solution:
    def __init__(self, f):
        self.found = f
        self.unified = set([])

    def humanize(self):
        if not self.found:
            return 'fail'
        res = 'success\n'
        for (a,b) in self.unified:
            res += a.humanize() + ' = ' + b.humanize() + '\n'
        return res

def unify(fol1, fol2):
    return unify1(fol1, fol2, solution(True))

def unify1(fol1, fol2, curSol):
    if not curSol.found:
        return curSol
    if fol1.eq(fol2):
        return curSol
    if fol1.is_var():
        return unifyVar(fol1, fol2, curSol)
    if fol2.is_var():
        return unifyVar(fol2, fol1, curSol)
    if fol1.is_const() or fol2.is_const():
        return solution(False)
    if fol1.name != fol2.name or len(fol1.children) != len(fol2.children):
        return solution(False)
    for arg1, arg2 in itertools.izip(fol1.children, fol2.children):
        curSol = unify1(arg1, arg2, curSol)
        if not curSol.found:
            return curSol
    return curSol

def unifyVar(var, func, curSol):
    for (a,b) in curSol.unified:
        if var.eq(a):
            return unify1(b, func, curSol)
    func = subst(curSol, func)
    if occursIn(var, func): # ------------ make sure of definition
        return solution(False)
    curSol.unified.add((var, func))
    for a,b in curSol.unified:
        subst(curSol, b)
    return curSol

def subst(curSol, func):
    if func.is_const():
        return func
    if func.is_var():
        for a,b in curSol.unified:
            if a.is_var() and a.name == func.name:
                return b
        return func
    newChildren = []
    for arg in func.children:
        newChildren.append(subst(curSol, arg))
    func.children = newChildren
    return func

def occursIn(var, func):
    if func.is_const():
        return False
    if func.is_var():
        if func.name == var.name:
            return True
        return False
    for arg in func.children:
        if occursIn(var, arg):
            return True
    return False

def test1():
    return unify(fn('P', var('x'), fn('g',var('x')), fn('g',fn('f',const('a')))),fn('P', fn('f', var('u')), var('v'), var('v'))).humanize()

def test2():
    return unify(fn('P', const('a'), var('y'), fn('f', var('y'))),fn('P', var('z'), var('z'), var('u'))).humanize()

def test3():
    return unify(fn('f', var('x'), fn('g', var('x')), var('x')), fn('f', fn('g', var('u')), fn('g', fn('g', var('z'))), var('z'))).humanize()

print unify(const('x'),const('a')).humanize()
print unify(fn('P', var('x'), fn('g',var('x')), fn('g',fn('f',const('a')))),fn('P', fn('f', var('u')), var('v'), var('v'))).humanize()
print unify(fn('P', const('a'), var('y'), fn('f', var('y'))),fn('P', var('z'), var('z'), var('u'))).humanize()
print unify(fn('f', var('x'), fn('g', var('x')), var('x')), fn('f', fn('g', var('u')), fn('g', fn('g', var('z'))), var('z'))).humanize()
