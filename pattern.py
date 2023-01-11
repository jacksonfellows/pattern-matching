def islist(pattern):
    return type(pattern) == list or type(pattern) == tuple

def isatom(pattern):
    return not islist(pattern)

class Constant():
    def __init__(self, val):
        self.val = val

    def __repr__(self):
        return f'Constant({repr(self.val)})'

class Capture():
    def __init__(self, var):
        self.var = var

    def __repr__(self):
        return f'Capture({repr(self.var)})'

class Sentinel():
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name

DOWN = Sentinel('DOWN')
UP = Sentinel('UP')
ANY = Sentinel('ANY')
AUTO = Sentinel('AUTO')

def index(expression, indices):
    if len(indices) > 0:
        return index(expression[indices[0]], indices[1:])
    else:
        return expression

def safeindex(expression, indices):
    try:
        return index(expression, indices)
    except IndexError:
        return None
    
class DFA:
    def __init__(self):
        self.states = []
        self.initial_state = None
        self.final_states = []

    def add_transition(self, prev_state, dest_state, edge):
        self.states[prev_state][edge] = dest_state

    def new_state(self):
        self.states.append(dict())
        return len(self.states) - 1

    def compile_pattern(self, pattern):
        self.initial_state = self.new_state()
        self.final_states.append(self.compile(pattern, self.initial_state))

    def compile_sequence(self, sequence, current_state):
        for pattern in sequence:
            current_state = self.compile(pattern, current_state)
        return current_state

    def compile(self, pattern, current_state):
        if isatom(pattern):
            final = self.new_state()
            if pattern == '_':
                self.add_transition(current_state, final, ANY)
            else:
                self.add_transition(current_state, final, Constant(pattern))
            return final
        else:
            if pattern[0] == '_':
                final = self.new_state()
                self.add_transition(current_state, final, Capture(pattern[1]))
                return final
            elif pattern[0] == 'or':
                a = self.compile(pattern[1], current_state)
                b = self.compile(pattern[2], current_state)
                final = self.new_state()
                self.add_transition(a, final, AUTO)
                self.add_transition(b, final, AUTO)
                return final
            elif pattern[0] == '*':
                a = self.compile(pattern[1], current_state)
                self.add_transition(a, current_state, AUTO)
                return current_state
            elif pattern[0] == '+':
                return self.compile_sequence((pattern[1], ('*', pattern[1])), current_state)
            else:
                start = self.new_state()
                self.add_transition(current_state, start, DOWN)
                end = self.compile_sequence(pattern, start)
                final = self.new_state()
                self.add_transition(end, final, UP)
                return final

    def eval(self, expression):
        indices = []
        state = None
        newstate = self.initial_state
        captures = {}
        while newstate != state:
            state = newstate
            for edge,dest in self.states[state].items():
                print(f'in state {state} looking at {edge},{dest} with {safeindex(expression, indices)} and {indices}')
                if edge is AUTO:
                    newstate = dest
                elif isinstance(edge, Constant):
                    try:
                        subexpression = index(expression, indices)
                        if edge.val == subexpression:
                            if len(indices) > 0:
                                indices[-1] += 1
                            newstate = dest
                    except IndexError:
                        pass
                elif edge is ANY:
                    try:
                        subexpression = index(expression, indices)
                        if len(indices) > 0:
                            indices[-1] += 1
                        newstate = dest
                    except IndexError:
                        pass
                elif isinstance(edge, Capture):
                    try:
                        subexpression = index(expression, indices)
                        if edge.var not in captures or subexpression == captures[edge.var]:
                            if len(indices) > 0:
                                indices[-1] += 1
                                captures[edge.var] = subexpression
                                newstate = dest
                    except IndexError:
                        pass
                elif edge is DOWN:
                    if islist(index(expression, indices)):
                        indices.append(0)
                        newstate = dest
                elif edge is UP:
                    if len(index(expression, indices[:-1])) == indices[-1]:
                        indices.pop()
                        if len(indices) > 0:
                            indices[-1] += 1
                        newstate = dest
        return state in self.final_states, captures
