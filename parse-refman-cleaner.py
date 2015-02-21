#!/usr/bin/env python3
import re
import sys
from pyparsing import nestedExpr, ParseResults, ParseException

TACTICS_PREPROCESSING = [('$n$', r'\n'), (r'\_', '_'), (r'\\', ''), (r'\ ', ' '), (r'\{', 'LBRACE'), (r'\}', 'RBRACE'),
                         ('~', ' '), ("''", ''), ('``', ''), ('\\\n', '\n')]

TACTICS_PREPROCESSING_RE = [(re.compile(r), s) for r, s in
                            [(r'\\([a-zA-Z]+) *{', r'{\\\1 '),
                             # (r'[_\^]{', r'{\\script '),
                             # (r'[_\^](.)', r'{\\script \1}'),
                             (r'\$[^\$]*\$', ''),
                             (r'}{([\,])}', r' {\\separator \1}}'),
                             (r'([^\\])%.*', r'\1'),
                             (r'\\%', r'%'),
                             (r'\\l?dots', r' \\ldots '),
                             (r' *([^a-zA-Z_<>!:\\]) *', r' \1 ')]] # This last one should be tokenizer options <- -> eqn: ! _

TACTICS_POSTPROCESSING_RE = [(re.compile(r), s) for r, s in
                             [(r' *([\-\[\(]) *', r' \1'),
                              (r' *([\]\)\.\,\!=]) *', r'\1 '),
                              (r' *([\%]) *', r'\1'),
                              (r'eqn: *', 'eqn:'),
                              ('LBRACE', '{'),
                              ('RBRACE', '}')]]


def behead(tup)           : return tup[1:]
def bebody(tup)           : return tup[:1]
def forget(_)             : return ()
def stringify(tup)        : return ' '.join(tup)
def behead_stringify(tup) : return stringify(tup[1:])
def keywordize(tup) :
    assert len(tup) == 2
    return '\\' + tup[1].rstrip('\\')

ACTIONS = {'tt':          behead,
           'texttt':      behead,
           'mbox':        behead,
           'num':         bebody,
           'ident':       bebody,
           'term':        bebody,
           'vref':        bebody,
           'qualid':      bebody,
           'bindinglist': bebody,
           'binder':      bebody,
           'tacindex':    forget,
           'comindex':    forget,
           'optindex':    forget,
           'label':       forget,
           'script':      forget,
           'separator':   forget, #TODO
           'sl':          keywordize,
           'nterm':       keywordize,
           'ldots':       stringify,
           'nelist':      behead_stringify,
           'nelistnosep': behead_stringify,
           'tacticdef':   behead_stringify}

ID_PATTERN = re.compile('@{([^}]+)}')

def preprocess_tactic(tactic):
    for pair in TACTICS_PREPROCESSING:
        tactic = tactic.replace(*pair)

    for r, sub in TACTICS_PREPROCESSING_RE:
        tactic = r.sub(sub, tactic)

    return tactic

def format_hole(kwd):
    return "@{{{}}}".format(kwd)

def pluralize(ident):
    if not ID_PATTERN.match(ident):
        # print("Multi-patterns dot pattern:", ident)
        # raise ConversionError
        return re.sub(ID_PATTERN, r'@{\1++}', ident)
    return re.sub(ID_PATTERN, r'@{\1+}', ident)

def replace_dot_pattern(s, pivot, transform):
    while True:
        pivot_pos = s.find(pivot)
        if pivot_pos == -1:
            return s

        left_end, right_start = pivot_pos, pivot_pos + len(pivot)
        for pattern_len in range(-left_end, 0):
            left_start, right_end = left_end + pattern_len, right_start - pattern_len
            if s[right_start:right_end] == s[left_start:left_end]:
                s = s[:left_start] + str(transform(s[left_start:left_end])) + s[right_end:]
                break
        else:
            print("Invalid dots pattern:", s)
            raise ConversionError

def postprocess_tactic(tactic):
    tactic = re.sub(r'[, ]*@{ldots}[, ]*', ' ... ', tactic)
    tactic = replace_dot_pattern(tactic, ' ... ', pluralize)
    for r, sub in TACTICS_POSTPROCESSING_RE:
        tactic = r.sub(sub, tactic)
    return tactic

def next_occ(doc, start, symbols):
    pos = None
    for symb in symbols:
        symb_pos = doc.find(symb, start)
        if pos == None or 0 <= symb_pos < pos:
            pos = symb_pos
    return pos

TACTIC_MARKER = r'\tacticdef'

def find_tactic(doc, start):
    depth, end = 0, start
    while depth >= 0:
        end = next_occ(doc, end + 1, '{}')
        if doc[end] == '{':
            depth += 1
        else:
            depth -= 1
    return end

def find_tactics(doc):
    end = 0
    while True:
        start = doc.find(TACTIC_MARKER, end + 1)
        if start == -1:
            break

        end = find_tactic(doc, start)
        yield start, doc[start:end]

def parse_to_sexp(parse):
    if isinstance(parse, ParseResults):
        return tuple(parse_to_sexp(x) for x in parse)
    else:
        return parse

NESTED_PARSER = nestedExpr(opener='{', closer='}')

def tactic_to_sexp(tactic):
    parse = NESTED_PARSER.parseString("{" + tactic + "}")
    tuplified = parse_to_sexp(parse)
    return tuplified[0]

class ConversionError(Exception):
    pass

def sexp_to_string(sexp):
    if not isinstance(sexp, tuple):
        if not isinstance(sexp, str):
            print("Invalid element:", sexp, file=sys.stderr)
            raise ConversionError
        if sexp[0] == '\\':
            sexp = format_hole(sexp[1:])
        return sexp

    if len(sexp) == 0:
        return None

    if len(sexp) == 1:
        return sexp_to_string(sexp[0])

    head = sexp[0]

    if head[0] != '\\':
        print("Invalid macro:", sexp, file=sys.stderr)
        raise ConversionError

    head = head[1:]
    if head not in ACTIONS:
        print("Unknown sexp:", sexp, file=sys.stderr)
        raise ConversionError

    sexp = tuple(sexp_to_string(arg) for arg in sexp)
    sexp = tuple(arg for arg in sexp if arg != None)
    sexp = ACTIONS[head](sexp)
    return sexp_to_string(sexp)

def tactic_to_abbrev(line, tactic):
    try:
        cleaned   = preprocess_tactic(tactic)
        sexp      = tactic_to_sexp(cleaned)
        preabbrev = sexp_to_string(sexp)
        abbrev    = postprocess_tactic(preabbrev)
        return abbrev
    except (ConversionError, ParseException):
        print("{}: `{}...`".format(line, tactic[:min(len(tactic), 40)].replace('\n', '')))
        return None

def main():
    path = "/build/coq/doc/refman/RefMan-oth.tex"
    path = "/build/coq/doc/refman/RefMan-tac.tex"

    with open(path) as source:
        doc = source.read()
        tactics = find_tactics(doc)
        abbrevs = [tactic_to_abbrev(line, tac) for line, tac in tactics]
        lisp_constant = ("(defconst company-coq-auto-extracted-tactics\n" +
                         "  '(" + "\n    ".join('"' + abbrev + '"' for abbrev in abbrevs if abbrev) + "))")

    WRITE = True
    if WRITE:
        with open('./company-coq-abbrev-tactics.el.template') as template:
            with open('./company-coq-abbrev-tactics.el', mode='w') as output:
                output.write(template.read().replace('$CODE$', lisp_constant))
    else:
        for abbrev in sorted(abbrevs):
            print(abbrev)

main()
