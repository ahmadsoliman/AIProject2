from node import *

# applies various normalizations
def normalize(root, restrict_to = None):
    if restrict_to is not None and root.kind != restrict_to: pass
    # a <=> b :::: a ==> b ^ b ==> a
    elif root.kind == '<=>':
        root.kind = '^'
        root2 = root.clone()
        child1 = node('==>', *root.children)
        child2 = node('==>', *list(reversed(root2.children)))
        root.children = [child1, child2]
    # a ==> b :::: ~a v b
    elif root.kind == '==>':
        root.kind = 'v'
        root.children[0] = node('~', root.children[0])
    # push the nots inwards
    elif root.kind == '~':
        child = root.children[0]
        # ~~a :::: a
        if child.kind == '~':
            child.consume_child()
            root.consume_child()
        # ~(a ^ b) :::: (~a v ~b)
        elif child.kind == '^':
            root.kind = 'v'
            root.children = [node('~', c) for c in child.children]
        # ~(a v b) :::: (~a ^ ~b)
        elif child.kind == 'v':
            root.kind = '^'
            root.children = [node('~', c) for c in child.children]
        # ~Ax[f(x)] :::: Ex[~f(x)]
        elif child.kind == 'A':
            root.kind = 'E'
            root.name = child.name
            root.children = [node('~', c) for c in child.children]
        # ~Ex[f(x)] :::: Ax[~f(x)]
        elif child.kind == 'E':
            root.kind = 'A'
            root.name = child.name
            root.children = [node('~', c) for c in child.children]

    for c in root.children:
        normalize(c, restrict_to)

# ensures root and children do not reuse variable names
def standardize(root):
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

    _standardize(root)

    for new_name in actions:
        for n in actions[new_name]:
            n.name = new_name

# eliminates existential quantifiers and replaces the quantified variables
# with functions of the in-scope variables
def skolemize(root):
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

    _skolemize(root)

def discard_universal_quantifiers(root):
    if root.kind == 'A':
        root.consume_child()
    for c in root.children:
        discard_universal_quantifiers(c)

# (a v (b ^ c)) :::: ((a v b) ^ (b v c))
def to_cnf(root):
    if root.kind in ['^', 'v']:
        if root.children[0] not in ['^', 'v']:
            atom, conn = root.children
        else:
            conn, atom = root.children
        # one child has to be a connective and the other a non-connetive
        if atom.kind not in ['^', 'v'] and conn.kind in ['^', 'v'] and conn.kind != root.kind:
            child1 = node(root.kind, atom, conn.children[0])
            child2 = node(root.kind, atom.clone(), conn.children[1])
            root.children = [child1, child2]
            root.kind = conn.kind

    for c in root.children:
        to_cnf(c)

def cnf_to_clause_form(root):
    if root.kind == 'v':
        if all_are(root.children, lambda c: c.kind != '^'):
            cf = [cnf_to_clause_form(c) for c in root.children]
            return cf[0] + cf[1]
    elif root.kind == '^':
        cf = []
        for child in root.children:
            if child.kind == '^':
                cf = cf + cnf_to_clause_form(child)
            else:
                cf = cf + [cnf_to_clause_form(child)]
        return cf
    else:
        return [root]


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

def fol_to_clause_form_cnf(root):
    n = root.clone()
    print "Converting %s to CNF\n" % n

    for op in ['<=>', '==>', '~']:
        print "Applying '%s' transformation" % op
        normalize(n, op)
        print "Result: %s\n" % n

    print "Standardizing"
    standardize(n)
    print "Result: %s\n" % n

    print "Skolemizing"
    skolemize(n)
    print "Result: %s\n" % n

    print "Discarding universal quantifiers"
    discard_universal_quantifiers(n)
    print "Result: %s\n" % n

    print "Converting to CNF"
    to_cnf(n)
    print "Result: %s\n" % n


    print "Converting CNF to Clause Form"
    cf = cnf_to_clause_form(n)
    print "Result: %s\n" % cf

    print "Standardizing Clause Form"
    standardize_clause_form(cf)
    print "Result: %s\n" % cf

    print "----------------------- Done ------------------------"

# example from lecture
tests = []
tests.append(
A('x',
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
                    fn('R', var('y'), var('x'))))))))

tests.append(
E('x',
    infix(
        fn('P', var('x')),
        '^',
        A('x',
            infix(
                fn('Q', var('x')),
                '==>',
                node('~', fn('P', var('x'))))))))

tests.append(
A('x',
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
                    fn('R', var('y'), var('x'))))))))

for test in tests:
    fol_to_clause_form_cnf(test)


