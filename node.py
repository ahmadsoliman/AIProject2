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

def A(*args): return node('A', *args)
def E(*args): return node('E', *args)
def var(name): return node('var', name)
def const(name): return node('const', name)
def fn(*args): return node('fn', *args)
def infix(c1, kind, c2): return node(kind, c1, c2)
