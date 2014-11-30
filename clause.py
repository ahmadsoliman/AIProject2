import itertools

# fn(x) for all members x of l returns true
def all_are(l, fn):
    return reduce(lambda acc, x: acc and fn(x), l, True)

class node(object):
    kinds =       ['const', 'var', 'fn', '~', '^', 'v', '==>', '<=>', 'A', 'E']

    def is_quantifier(self):
        return self.kind in ['A', 'E']
    def is_binary(self):
        return self.kind in ['^', 'v', '==>', '<=>']
    def is_unary(self):
        return self.kind == '~'
    def is_function(self):
        return self.kind == 'fn'
    def is_atom(self):
        return self.kind in ['const', 'var']
    def is_const(self):
        return self.kind == 'const'
    def is_var(self):
        return self.kind == 'var'


    def __init__(self, kind, *args):
        if kind not in self.kinds:
            raise Exception("Invalid kind " + kind)

        self.kind = kind
        self.name = ''
        self.children = []
        if isinstance(args[0], str): # it's a name
            self.name = args[0]
            self.children = list(args[1:])
        else:
            all_nodes = all_are(args, lambda a: isinstance(a, node))
            if all_nodes:
                self.children = list(args)
            else:
                raise Exception("Remaining arguments are not nodes!\n%s" % str(args))

        # sanity check
        self.assert_consistency()


    def eq(self, other):
        if self.kind != other.kind or self.name != other.name or len(self.children) != len(other.children):
            return False
        for arg1,arg2 in itertools.izip(self.children, other.children):
            if not arg1.eq(arg2):
                return False
        return True

    def humanize(self):
        if self.is_atom():
            return self.name
        # TODO
        if not self.is_function():
            return ''
        res = self.name + '('
        for arg in self.children:
            res += arg.humanize() + ','
        return res[:-1] + ')'

    def assert_consistency(self):
        if not self.is_consistent():
            msg = "Inconsistent!\nkind = %s\nname = %s\nchildren = %s" %\
                (self.kind, self.name, self.children)
            raise Exception(msg)

    def is_consistent(self):
        if self.is_atom():
            return len(self.children) == 0
        elif self.is_function():
            return len(self.children) > 0
        elif self.is_unary():
            return len(self.children) == 1
        elif self.is_binary():
            return len(self.children) == 2
        elif self.is_quantifier():
            return len(self.children) == 1
        else:
            raise Exception("This shouldn't be happening....")

    def clone(self):
        children = [child.clone() for child in self.children]
        return node(self.kind, self.name, *children)

    # become a different node
    def consume(self, n):
        self.kind = n.kind
        self.children = n.children
        self.name = n.name

    # removes self from the tree by becoming its own child
    def consume_child(self):
        if self.is_quantifier() or self.is_unary():
            self.consume(self.children[0])
        else:
            raise Exception('Cannot consume more than one child!')

    def __repr__(self):
        def wrap_child(c):
            if c.kind in ['const', 'var', 'fn', '~', 'A', 'E'] or\
                    (self.kind in ['^', 'v'] and c.kind == self.kind):
                return "%s" % c
            else:
                return "(%s)" % c

        if self.is_atom():
            return self.name
        elif self.is_function():
            return "%s(%s)" % (self.name, ", ".join([str(c) for c in self.children]))
        elif self.is_unary():
            return "%s%s" % (self.kind, wrap_child(self.children[0]))
        elif self.is_binary():
            return "%s %s %s" % (wrap_child(self.children[0]), self.kind, wrap_child(self.children[1]))
        elif self.is_quantifier():
            return "%s%s[%s]" % (self.kind, self.name, self.children[0])
        else:
            raise Exception("This shouldn't be happening....")

    # applies various normalizations
    def normalize(self, restrict_to = None):
        if restrict_to is not None and self.kind != restrict_to: pass
        # a <=> b :::: a ==> b ^ b ==> a
        elif self.kind == '<=>':
            self.kind = '^'
            self2 = self.clone()
            child1 = node('==>', *self.children)
            child2 = node('==>', *list(reversed(self2.children)))
            self.children = [child1, child2]
        # a ==> b :::: ~a v b
        elif self.kind == '==>':
            self.kind = 'v'
            self.children[0] = node('~', self.children[0])
        # push the nots inwards
        elif self.kind == '~':
            child = self.children[0]
            # ~~a :::: a
            if child.kind == '~':
                child.consume_child()
                self.consume_child()
            # ~(a ^ b) :::: (~a v ~b)
            elif child.kind == '^':
                self.kind = 'v'
                self.children = [node('~', c) for c in child.children]
            # ~(a v b) :::: (~a ^ ~b)
            elif child.kind == 'v':
                self.kind = '^'
                self.children = [node('~', c) for c in child.children]
            # ~Ax[f(x)] :::: Ex[~f(x)]
            elif child.kind == 'A':
                self.kind = 'E'
                self.name = child.name
                self.children = [node('~', c) for c in child.children]
            # ~Ex[f(x)] :::: Ax[~f(x)]
            elif child.kind == 'E':
                self.kind = 'A'
                self.name = child.name
                self.children = [node('~', c) for c in child.children]

        for c in self.children:
            c.normalize(restrict_to)

    # ensures self and children do not reuse variable names
    def standardize(self):
        # avail is the list of usable variable names
        avail = [chr(i) for i in range(97, 123)]

        # actions maps new-names to a list of nodes
        actions = {}
        # these actions will be done after the traversal

        def _standardize(n, renames = {}):
            # renames keeps track of the currently active renames
            # a rename is only applicable to levels of the tree that are
            # deeper than where the rename originated

            if n.is_quantifier():
                if n.name in avail: # this should happen once per traversal
                    avail.remove(n.name)
                else: # our variable is used!
                    if n.name in actions: # it was used as a rename
                        # give those nodes a another name so they don't use ours
                        new_new_name = avail.pop()
                        acts = actions[n.name]
                        actions[new_new_name] = acts
                        del actions[n.name]
                        renames[acts[0].name] = new_new_name
                    else: # it was used by a quantifier
                        # rename the current node
                        new_name = avail.pop()
                        renames[n.name] = new_name
                        actions[new_name] = [n]
            elif n.kind == 'var':
                if n.name in renames:
                    actions[renames[n.name]].append(n)

            # recursively standardize children
            for c in n.children:
                _standardize(c, renames)

            # restore the renames map by removing any rename we added
            if n.is_quantifier() and n.name in renames:
                del renames[n.name]

        _standardize(self)

        for new_name in actions:
            for n in actions[new_name]:
                n.name = new_name

    # eliminates existential quantifiers and replaces the quantified variables
    # with functions of the in-scope variables
    def skolemize(self):
        actions = {}
        avail = ['f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n']
        avail.reverse()

        def _skolemize(n, fn_args = [], skolems = {}):
            if n.kind == 'A':
                fn_args.append(n.name)
            elif n.kind == 'E':
                children = [node('var', a) for a in fn_args]
                skolems[n.name] = node('fn', avail.pop(), *children)
            elif n.kind == 'var':
                if n.name in skolems:
                    n.consume(skolems[n.name].clone())

            for c in n.children:
                _skolemize(c, fn_args, skolems)

            if n.kind == 'A':
                fn_args.pop()
            elif n.kind == 'E':
                del skolems[n.name]
                n.consume_child()

        _skolemize(self)

    def discard_universal_quantifiers(self):
        if self.kind == 'A':
            self.consume_child()
        for c in self.children:
            c.discard_universal_quantifiers()

    # (a v (b ^ c)) :::: ((a v b) ^ (b v c))
    def to_cnf(self):
        if self.kind in ['^', 'v']:
            if self.children[0] not in ['^', 'v']:
                atom, conn = self.children
            else:
                conn, atom = self.children
            # one child has to be a connective and the other a non-connetive
            if atom.kind not in ['^', 'v'] and conn.kind in ['^', 'v'] and conn.kind != self.kind:
                child1 = node(self.kind, atom, conn.children[0])
                child2 = node(self.kind, atom.clone(), conn.children[1])
                self.children = [child1, child2]
                self.kind = conn.kind

        for c in self.children:
            c.to_cnf()

    def clause_form(self):
        if self.kind == 'v':
            if all_are(self.children, lambda c: c.kind != '^'):
                cf = [c.clause_form() for c in self.children]
                return cf[0] + cf[1]
        elif self.kind == '^':
            cf = []
            for child in self.children:
                if child.kind == '^':
                    cf = cf + child.clause_form()
                else:
                    cf = cf + [child.clause_form()]
            return cf
        else:
            return [self]


# NOTE destructive operation
def standardize_clause_form(cf):
    def find_vars(n):
        if n.kind == 'var': return [n]
        else:
            vs = []
            for fvs in [find_vars(c) for c in n.children]:
                vs = vs + fvs
            return vs

    varn = {}
    for conj in cf:
        used = []
        for disj in conj:
            for v in find_vars(disj):
                if v.name not in varn:
                    varn[v.name] = 0
                if v.name not in used:
                    varn[v.name] = varn[v.name] + 1
                    used.append(v.name)
                v.name = v.name + str(varn[v.name])

def A(*args): return node('A', *args)
def E(*args): return node('E', *args)
def var(name): return node('var', name)
def const(name): return node('const', name)
def fn(*args): return node('fn', *args)
def infix(c1, kind, c2): return node(kind, c1, c2)

orig = A('x',
        infix(
            fn('P', var('x')),
            '<=>',
            infix(
                fn('Q', var('x')),
                '^',
                E('y',
                    infix(
                        fn('Q', var('y')),
                        '^',
                        fn('R', var('y'), var('x')))))))

n = orig.clone()
print n
for op in ['<=>', '==>', '~']:
    n.normalize(op)
    print n

n.standardize()
print n

n.skolemize()
print n

n.discard_universal_quantifiers()
print n

n.to_cnf()
print n

cf = n.clause_form()
print cf

standardize_clause_form(cf)
print cf
