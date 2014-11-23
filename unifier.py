import itertools

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

class Solution:
  def __init__(self, found, unified=set([])):
    self.found = found
    self.unified = unified

  def humanize(self):
    res = ''
    for (a,b) in self.unified:
      res += a.humanize() + ' = ' + b.humanize() + '\n'
    return res

def unify(fol1, fol2):
  return unify1(fol1, fol2)

def unify1(fol1, fol2, curSol=Solution(True)):
  if not curSol.found:
    return curSol
  if fol1.eq(fol2):
    return curSol
  if fol1.type == Function.VAR:
    unifyVar(fol1, fol2, curSol)
  if fol2.type == Function.VAR:
    unifyVar(fol2, fol1, curSol)
  if fol1.type == Function.ATOM or fol2.type == Function.ATOM:
    return Solution(False)
  if fol1.name != fol2.name or len(fol1.args) != len(fol2.args):
    return Solution(False)
  for arg1, arg2 in itertools.izip(fol1.args, fol2.args):
    curSol = unify1(arg1, arg2, curSol)
    if not curSol.found:
      return curSol
  return curSol

def unifyVar(var, func, curSol):
  for (a,b) in curSol.unified:
    if var == b and a != b:
      return unify1(a, func, curSol)
  func = subst(curSol, func)
  if occursIn(var, func): # ------------ make sure of definition
    return Solution(False)
  curSol.unified.add((var, func))
  return curSol

def subst(curSol, func):
  if func.type == Function.ATOM:
    return func
  if func.type == Function.VAR:
    for a,b in curSol.unified:
      if a.type == Function.VAR and a.name == func.name:
        func = b
        break
    return func
  for arg in func.args:
    arg = subst(curSol, arg)
  return func

def occursIn(var, func):
  if func.type == Function.ATOM:
    return False
  if func.type == Function.Var:
    if func.name == var.name:
      return True
    return False
  for arg in func.args:
    if occursIn(var, arg):
      return True
  return False

def test1():
  return unify(Function("x", Function.VAR),Function("a", Function.ATOM)).humanize()
