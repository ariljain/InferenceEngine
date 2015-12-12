import sys
from pprint import pprint

class Term():
    '''Stores a FOL term for the form A(x,y,C) as
       predicate : A
       args : list([a,y,C])
    '''
    def __init__(self, term):
        open_brace = term.index('(')
        self.predicate = term[:open_brace]
        self.args = [a.strip() for a in term[open_brace+1:-1].split(',')]
        self.clause = term

    def __eq__(self, other):
        return self.predicate == other.predicate and self.args == other.args

    def neg(self):
        neg_term = ''
        
        if self.clause[0] == '~':
            return Term(self.clause[1:])
        else:
            return Term('~'+self.clause)

    def __str__(self):
        return self.clause

    def __repr__(self):
        return self.clause

    def __hash__(self):
        "Need a hash method so Term can live in dicts."
        return hash(self.predicate) ^ hash(tuple(self.args))


class KB():
    '''Stores all the clases and the facts
       You can TELL KB a fact / clause
       You can ASK KB if a query can be inferred from the KB
       If every variable in each rule of the proving process 
          cannot be unified with a Constant, then returns False on ASK
    '''
    def __init__(self):
        self.clauses = {}
        self.facts = {}


    def tell(self, sentence):
        '''Checks if the given sentence is a predicate or fact
           Adds to appropriate dictionary
        '''
        if isFact(sentence):
            self.addFact(sentence)
        else:
            self.addClause(sentence)


    def addFact(self, sentence):
        '''Adds a fact to the KB
           Uses the predicate as the key
           For each key add to the list of corresponding facts
        '''
        s = Term(sentence.strip())

        if s.predicate not in self.facts:
            self.facts[s.predicate] = []

        self.facts[s.predicate].append(sentence)


    def addClause(self, sentence):
        '''Adds a clause to the KB
           Uses implication predicate as key
           For each key add to the list of the corresponding rules
        '''
        conditionals, implication = sentence.split('=>')
        implication = Term(implication.strip())

        if implication.predicate not in self.clauses:
            self.clauses[implication.predicate] = []

        self.clauses[implication.predicate].append(sentence)


    def get_goal_clauses(self, term):
        '''Returns a dictionary of clauses where implication matches the goal
        '''
        rules = []

        if term.predicate in self.facts:
            rules.extend(self.facts[term.predicate])

        if term.predicate in self.clauses:
            rules.extend(self.clauses[term.predicate])
        
        return rules



    def ask(self, query):
        '''Returns True if the query can be inferred using KB, False otherwise
        '''
        q = Term(query.strip())

        visited_facts = set()

        sub = dict()

        for s in backChain_OR(self, q, sub, visited_facts):
            return True


def get_cond_impl(sentence):
    '''Returns a list of conditionals and the implication
       if the given sentence is an inference rule
    '''
    if '=>' not in sentence:
        return None, Term(sentence)
    else:
        conditionals, implication = sentence.split('=>')
        implication = Term(implication.strip())
        conditionals = [Term(c.strip()) for c in conditionals.split('^')]
        return conditionals, implication


def standardize_var(conditionals, implication, app):
    '''Returns a sentence with variables standardized
    '''
    rhs = implication.predicate+'('

    for a in implication.args:
        if isVar(a):
            rhs += a+app+','
        else:
            rhs += a+','

    rhs = rhs[:-1]
    rhs += ')'
    
    lhs = ''

    for c in conditionals:
        lhs += c.predicate+'('
        for a in c.args:
            if isVar(a):
                lhs += a+app+','
            else:
                lhs += a+','
        lhs = lhs[:-1]
        lhs += ')^'
    
    lhs = lhs[:-1]

    return lhs + ' => ' + rhs


STANDARDIZING_VAR = 0
def standardize(rule):
    global STANDARDIZING_VAR
    STANDARDIZING_VAR += 1

    if '=>' not in rule:
        return rule
    else:
        conditionals, implication = rule.split('=>')
        implication = Term(implication.strip())
        conditionals = [Term(c.strip()) for c in conditionals.split('^')]

        std_rule = standardize_var(conditionals, implication, str(STANDARDIZING_VAR))

        return std_rule


def substitute(s, t):
    '''Return a new term with argument variables replaced
       with their corresponding values from the substitution list s
    '''
    if isinstance(t, list):
        return [substitute(s, c) for c in t]

    elif isinstance(t, str) and not isVar(t):
        return t

    elif isinstance(t, str) and isVar(t):
        if t in s:
            return s[t]
        else:
            return t

    else:
        new_args = [substitute(s, a) for a in t.args]
        new_args = ','.join(a for a in new_args)
        new_args = '('+new_args+')'
        return Term(t.predicate+new_args)


def backChain_OR(MyKB, goal, theta, vfs):

    if isFact(str(goal)) and str(goal) in vfs:
        return None
    else:
        vfs.add(str(goal))

    if goal.predicate in MyKB.facts and str(goal) in MyKB.facts[goal.predicate]:
        yield theta

    rules = MyKB.get_goal_clauses(goal)

    if len(rules) <= 0:
        return theta


    for rule in rules:
        lhs, rhs = get_cond_impl(standardize(rule))

        sub = unify(rhs, goal, theta)

        if not sub and rhs == goal:
            sub['dummy'] = 'dummy'

        if sub:
            for theta1 in backChain_AND(MyKB, lhs, sub, vfs):
                yield theta1


def backChain_AND(MyKB, sub_goals, theta, vfs):

    if theta is None:
        yield theta
    
    elif not sub_goals:
        yield theta
    
    else:
        first, rest = sub_goals[0], sub_goals[1:]

        new_goal = substitute(theta, first)
        
        for theta1 in backChain_OR(MyKB, new_goal, theta, vfs):
            for theta2 in backChain_AND(MyKB, rest, theta1, vfs):
                yield theta2


def unify(t1, t2, s):
    '''Returns substitution list after unification of terms t1 and t1
       Returns None if unification is not possible
    '''
    if type(t1) == type(t2) and t1 == t2:
        return s

    elif not isinstance(t1, Term) and isVar(t1):
        return unify_var(t1, t2, s)

    elif not isinstance(t2, Term) and isVar(t2):
        return unify_var(t2, t1, s)

    elif isinstance(t1, Term) and isinstance(t2, Term):
        return unify(t1.args, t2.args, unify(t1.predicate, t2.predicate, s))

    elif isinstance(t1, str) or isinstance(t2, str):
        return None

    elif isinstance(t1, list) and isinstance(t2, list) and len(t1)==len(t2):
        if not t1:
            return s
        else:
            return unify_list(t1, t2, s)

    else:
        return None


def unify_var(v, t, s):
    if s:
        if v in s:
            return unify(s[v], t, s)
        else:
            new_s = s.copy()
            new_s[v] = t
            return new_s
    else:
        new_s = dict()
        new_s[v] = t
        return new_s
    

def unify_list(l1, l2, s):

    for i in range(len(l1)):
        if not isVar(l1[i]) and not isVar(l2[i]) and l1[i] != l2[i]:
            return None
        else:
            s = unify(l1[i], l2[i], s)

    return s


def isFact(sentence):
    '''Return True if the sentence is a fact
       False otherwise
    '''
    if '=>' not in sentence:
        s = Term(sentence.strip())

        #check if all arguments are constants
        if all(a[0].isupper() for a in s.args):
            return True

    return False


def isVar(arg):
    '''Returns True if the arg is a variable
    '''
    if isinstance(arg, str) and arg.islower():
        return True
    else:
        return False


if __name__ == '__main__':
    infile = str(sys.argv[2])
    f = open(infile,'r')

    num_queries = int(f.readline())
    all_queries = []

    #build a list of queries
    for i in range(num_queries):
        all_queries.append(str(f.readline()).strip())

    num_clauses = int(f.readline())

    #instantiate a new knowledge base
    kb = KB()

    #populate KB with facts and inference rules
    for i in range(num_clauses):
        kb.tell(str(f.readline()).strip())

    f.close()


    g = open('output.txt','w')

    #ask the KB if the query can be inferred
    for query in all_queries:
        response = kb.ask(query)

        if response:
            g.write('TRUE\n')
        else:
            g.write('FALSE\n')
    

    g.close()
