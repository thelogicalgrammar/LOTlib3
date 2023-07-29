from LOTlib3.Grammar import Grammar
from LOTlib3.Samplers.MetropolisHastings import MetropolisHastingsSampler
from LOTlib3.Hypotheses.LOTHypothesis import LOTHypothesis
from LOTlib3.DataAndObjects import FunctionData
from LOTlib3.Eval import primitive, register_primitive

from collections import Counter
from stitch_core import compress
from math import log, exp
import re
from copy import deepcopy

from LOTlib3.StitchBindings.python_to_stitch import python_to_stitch, parse_function_calls
from LOTlib3.StitchBindings.stitch_to_python import stitch_to_python, abstraction_to_python


def process_name(name):
    name, *_ = name.split('(')
    return name


def get_rules_dict(grammar):
    # infer the types of the variables
    rules = [
        x.get_rule_signature() 
        for x 
        in grammar.get_all_rules()
    ]
    
    rules_dict = {
        process_name(name): [selftype, args]
        for selftype, name, *args 
        in rules
    }

    return rules_dict


def flatten_multiple_arguments(arg):
    if isinstance(arg, list):
        if isinstance(arg[0], list):
            return flatten_multiple_arguments([*arg[0], *arg[1:]])
        else:
            return [
                flatten_multiple_arguments(a) 
                for a in arg
            ]
    else:
        return arg


def recursive_flatten(arg):
    if arg == []:
        return arg
    if isinstance(arg[0], list):
        return recursive_flatten(arg[0]) + recursive_flatten(arg[1:])
    return arg[:1] + recursive_flatten(arg[1:])


def infer_types(arg, rules_dict, known_type):
    """
    Get a parsed formula (in python notation)
    and constructs its type.

    The main complication here is that we need
    to go to the leafs to find the types of the
    arguments of the top level lambdas,
    and then pass them again bottom up to 
    figure out the type of the whole formula.

    Examples of input/outputs:

    fn_0 --> lambda y0: lneg_(bin_subseteq_(y0)(y0)) 
    ['SET', 'BOOL'], types of variables
    
    fn_1 --> lambda y0: lambda y1: intleq_(y1)(bin_cardinality_(y0))
    ['SET', 'INT', 'BOOL'], types of variables
    """
    
    # the type of a lambda is a function 
    # from the type of its argument 
    # to the type of its body
    # First value could look like 'lambda y0:'
    if arg[0].startswith('lambda'):
        types_arguments, new_vartypes = infer_types(
            *arg[1:],
            rules_dict,
            known_type=None
        )
        # get actual variable
        var = arg[0].strip()[:-1].split(' ')[1]
        # get type of variable
        vartype = new_vartypes[var]
        # type of whole lambda is type of body 
        # after all arguments have been applied
        self_type = types_arguments[0]
        return [vartype, types_arguments], new_vartypes

    # if it is a list that does not start with a lambda,
    # first argument is the primitive
    # and subsequent ones the arguments
    # NOTE: This condition doesn't use known_type
    # argument because we can infer from arg[1:]
    elif isinstance(arg, list):
        # get types of arguments from type of operator
        self_type, known_arg_types = rules_dict[arg[0]]
        # initialize types of variables
        new_vartypes = dict()
        for x, known_type in zip(arg[1:], known_arg_types):
            ta, vt = infer_types(
                x, 
                rules_dict,
                known_type=known_type
            )
            new_vartypes.update(vt)
        return [self_type], new_vartypes

    # if this is a variable we can
    # pass the known type up
    # (known type is based on primitive
    # of which the function is an argument)
    elif arg.startswith('y'):
        return known_type, {arg: known_type}

    # otherwise, this is just a terminal
    else:
        return rules_dict[arg][0], dict()


def add_to_fname(name, to):
    return (
        name + 
        ''.join(['(%s)' for _ in range(len(to))])
    )


def expand_grammar(grammar, python_abstractions, weight):
    """
    Define a new grammar 
    that contains the abstractions in grammar
    and also the abstractions in results
    """
    
    rules_dict = get_rules_dict(grammar)
    new_grammar = deepcopy(grammar)
    for name, abstr in python_abstractions.items():
        parsed_abstr = parse_function_calls(
            abstr
        )
        flattened = flatten_multiple_arguments(parsed_abstr)
        inferred, _ = infer_types(
            flattened, 
            rules_dict,
            None
        )
        *to, nt = recursive_flatten(inferred)
        new_grammar.add_rule(
            nt=nt,
            name=add_to_fname(name, to),
            to=to,
            p=weight,
        )
    return new_grammar


def compress_and_transform(
            best_parsed,
            grammar,
            # how many hypotheses to compress per task
            n_per_task=5,
            eta_long=True,
            prefix='',
            best_names=None,
            # weight of new abstractions
            weight=1,
        ):

    if eta_long:
        additional_kwargs = {
            'eta_long': True,
            'utility_by_rewrite': True
        }
    else:
        additional_kwargs = dict()

    new_basename = f'fn_{prefix}_'
    
    # compress the hypotheses with stitch
    res = compress(
        best_parsed, 
        iterations=10, 
        max_arity=2,
        # NOTE: See https://stitch-bindings.readthedocs.io/en/stable/compression_objectives.html#compression-objectives
        # tasks=best_names,
        allow_single_task=True,
        cost_ivar=100,
        cost_var=100,
        abstraction_prefix=new_basename,
        **additional_kwargs
    )
    
    # convert the abstractions into python
    python_rewritten = [
        abstraction_to_python(x.__str__())
        for x
        in res.abstractions
    ]
    
    # add the found abstractions 
    # to LOTlib3 primitives
    # and to the new grammar
    python_abstractions = dict()
    locals = dict()
    new_grammar = deepcopy(grammar)
    
    for i, abstraction in enumerate(res.abstractions):
        
        rules_dict = get_rules_dict(new_grammar)
        
        # convert abstraction to python syntax
        python_fn = abstraction_to_python(
            abstraction.__str__()
        )
        name = f'{new_basename}{i}'
        meaning = eval(
            python_fn,
            None,
            locals
        )

        # meaning.__name__ = name
        # this must be done before the 
        register_primitive(
            meaning,
            name=name
        )

        # get parsed expression
        flattened = flatten_multiple_arguments(
            parse_function_calls(
                python_fn
            )
        )

        # inferred type
        inferred, _ = infer_types(
            flattened, 
            rules_dict,
            None
        )
        *to, nt = recursive_flatten(inferred)
        
        new_grammar.add_rule(
            nt=nt,
            name=add_to_fname(name, to),
            # if there's no arguments
            # it's not a function at all
            to=None if len(to)==0 else to,
            p=weight,
        )
        
        try:
            # in case the following functions
            # use this function
            # add it to the locals dict for eval(...)
            locals[name] = meaning
            python_abstractions[name] = python_fn
            
        except AttributeError:
            print('Not storing ', name, python_fn)
    
    return res, python_abstractions, python_rewritten, new_grammar


def infer(h, datas, n_steps):
    # run the inference
    counters = []
    for i, data in enumerate(datas):
        count = Counter()
        for i, h_i in enumerate(MetropolisHastingsSampler(h, data, steps=n_steps)):
            count[h_i] += 1
            if i%1000==0:
                print(i, end=', ')
        print('Done with ', i)
        counters.append(count)
    return counters


def infer_and_compress(Hypothesis, datas, grammar, n_steps=10000, 
                       n_per_task=5, eta_long=True, 
                       abstr_index=''):

    h = Hypothesis(
        grammar=grammar
    )
    
    counters = infer(
        h, 
        datas, 
        n_steps
    )
    
    # get the best hypotheses for each task
    best = []
    best_counts = []
    best_names = []
    for i, c in enumerate(counters):
        best_hs, counts_hs = list(zip(*c.most_common(n_per_task)))
        best += best_hs
        best_counts += counts_hs
        best_names += [f'task_{i}']*n_per_task
    
    # parse the hypotheses into stitch
    best_parsed = [
        python_to_stitch(x.__str__())
        for x in best
    ]

    res, python_abstractions, python_rewritten, new_grammar = compress_and_transform(
        best_parsed,
        grammar,
        n_per_task=n_per_task,
        eta_long=eta_long,
        prefix=abstr_index,
        best_names=best_names,
    )

    return {
        'best': best, 
        'best_counts': best_counts, 
        'best_names': best_names, 
        'best_parsed': best_parsed, 
        'python_rewritten': python_rewritten, 
        'python_abstractions': python_abstractions,
        'stitch_res': res,
        'stitch_abstractions': res.abstractions,
        'newgrammar': new_grammar
    }

