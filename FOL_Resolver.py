from collections import defaultdict
from copy import deepcopy

negate_expression = lambda expr: '~'+expr if expr[0] != '~' else expr[1:]

class Knowledge_Base:
    def __init__(self):
        self.facts = []
        self.rules = []
        self.facts_mapping = {}
        self.rules_mapping = {}
        self.info = {}
    
    def __len__(self):
        return len(self.info)


class Argument:
    def __init__(self, arg_value):
        self.name = arg_value
        self.is_variable = True if len(self.name) == 1 and self.name.islower() else False
        self.is_assigned = False if self.is_variable else True
        self.value = None if self.is_variable else arg_value


class Predicate:
    def __init__(self, predicate, argument_dict={}):
        arg_list = predicate.split('(')
        self.name = arg_list[0]
        self.is_negate = False
        if '~' in self.name:
            self.name = self.name[1:]
            self.is_negate = True
        arguments = arg_list[1].split(')')[0].split(',')
        self.arguments = [Argument(arg) for arg in arguments]
        if argument_dict:
            # p(arguments)
            self.arguments = [argument_dict[arg] if arg in argument_dict else Argument(arg) for arg in arguments]
        self.predicate = self.name if not self.is_negate else negate_expression(self.name)
        self.predicate += '('+','.join([arg.name for arg in self.arguments])+')'
        self.is_fact = all([arg.name[0].isupper() for arg in self.arguments]) 
    
    def invert_negation(self):
        self.is_negate = not self.is_negate
        self.predicate = negate_expression(self.predicate)


class Expression:
    def __init__(self, expression=None, predicate_list=list(), arguments=dict()):
        self.expression = expression
        if self.expression:
            self.predicate_list = []
            # self.arguments = dict()
            expressions = self.expression.split('|')
            for expr in expressions:
                predicate = Predicate(expr)
                self.predicate_list.append(predicate)
                # for arg in predicate.arguments:
                #     if arg.value not in self.arguments:
                #         self.arguments[arg.value] = arg
        else:
            self.predicate_list = [Predicate(pred.predicate, arguments) for pred in predicate_list]
            self.expression = '|'.join([pred.predicate for pred in self.predicate_list])
            # self.arguments = {arg.name:arg for arg in arguments.values()}
        # self.operator = '|' if len(self.predicate_list)>1 else None

    def __len__(self):
        return len(self.predicate_list)

def convert_to_cnf(expression, negate=False):
    # p(expression)
    if '=>' in expression:
        # Remove Implication
        statements = expression.split('=>')
        statements[0] = convert_to_cnf(statements[0], negate=True)
        return '|'.join(statements)
    if '&' in expression:
        statements = expression.split('&')
        if negate:
            statements = [negate_expression(statement) for statement in statements]
        return '|'.join(statements)
    return negate_expression(expression) if negate else expression

   
def facts_or_rules():
    for key, expr in knowledge_base.info.items():
        is_rule = False
        if len(expr) == 1:
            for arg in expr.predicate_list[0].arguments:
                if arg.is_variable:
                    if key not in knowledge_base.rules_mapping:
                        knowledge_base.rules.append(expr)
                        knowledge_base.rules_mapping[key] = expr
                    break
            else:
                if key not in knowledge_base.facts_mapping:
                    pred = expr.predicate_list[0]
                    knowledge_base.facts.append(pred)
                    knowledge_base.facts_mapping[key] = pred
        else:
            if key not in knowledge_base.rules_mapping:
                knowledge_base.rules.append(expr)
                knowledge_base.rules_mapping[key] = expr


def read_input(knowledge_base):
    queries = []    
    with open('input.txt', 'r') as f:
        file = list(f)
    f.close()
    num_queries = int(file[0].rstrip('\n').rstrip('\r'))
    for idx in range(1, num_queries+1):
        queries.append(Predicate(file[idx].rstrip('\n').rstrip('\r')))
    num_statements = int(file[num_queries+1].rstrip('\n').rstrip('\r'))
    for idx in range(num_queries+2, num_queries+num_statements+2):
        statement = file[idx].rstrip('\n').rstrip('\r').replace(' ', '')
        expr = Expression(convert_to_cnf(statement))
        knowledge_base.info[expr.expression] = expr
    facts_or_rules()
    return queries


def build_knowledge_base():
    facts_or_rules()
    # infered_facts = deepcopy(knowledge_base.facts)
    while knowledge_base.facts:
        curr_fact = knowledge_base.facts.pop(0)
        for curr_rule in knowledge_base.rules:
            for curr_pred in curr_rule.predicate_list:
                unify, variable_unification_assignment = can_be_unified(curr_fact, curr_pred)
                if unify:
                    unify_fact(curr_rule, curr_pred, variable_unification_assignment)


def unify_fact(rule, predicate, variable_mapping):
    unresolved_pred_list = [pred for pred in rule.predicate_list if pred.predicate != predicate.predicate]
    resolved_facts = Expression(predicate_list=unresolved_pred_list, arguments=variable_mapping)

    if len(resolved_facts.predicate_list)==1:
        if resolved_facts.expression not in knowledge_base.facts_mapping:
            knowledge_base.facts.append(resolved_facts.predicate_list[0])
            knowledge_base.facts_mapping[resolved_facts.expression] = resolved_facts.predicate_list[0]
    else:
        if resolved_facts.expression not in knowledge_base.rules_mapping:
            knowledge_base.rules.append(resolved_facts)
            knowledge_base.rules_mapping[resolved_facts.expression] = resolved_facts
    
    if resolved_facts.expression not in knowledge_base.info:
        knowledge_base.info[resolved_facts.expression] = resolved_facts
	

def can_be_unified(predicate_1, predicate_2):
    # Check if unification is possible
    can_unify = predicate_1.name == predicate_2.name and len(predicate_1.arguments) == len(predicate_2.arguments) and predicate_1.is_negate != predicate_2.is_negate
    unification_assignment = {}
    if can_unify:
        # Build variable unification mapping
        for arg1, arg2 in zip(predicate_1.arguments, predicate_2.arguments):
            if not arg1.is_variable and arg2.is_variable:
                unification_assignment[arg2.name] = arg1
            elif not arg1.is_variable and not arg2.is_variable and (arg1.value == arg2.value):
                continue
            else:
                # Cannot be unified
                can_unify = False
                unification_assignment = {}
                break
    return can_unify, unification_assignment


def forward_chain():
    prev_kb_size = len(knowledge_base)
    while True:
        build_knowledge_base()
        kb_size = len(knowledge_base)
        if prev_kb_size == kb_size:
            break
        prev_kb_size = kb_size
    

def resolve():
    for query in queries:
        # query.invert_negation()
        output = query.predicate in knowledge_base.facts_mapping
        output = 'TRUE\n' if output else 'FALSE\n'
        with open('output.txt', 'a+') as f:
            f.write(output)
    f.close()


knowledge_base = Knowledge_Base()
queries = read_input(knowledge_base)
forward_chain()
resolve()