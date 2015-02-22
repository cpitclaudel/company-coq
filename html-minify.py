import re
import sys
import errno
from os import mkdir, rename
from subprocess import call
from os.path import split, join
from bs4 import BeautifulSoup


B36 = '0123456789abcdefghijklmnopqrstuvwxyz'

def b36(num):
    s = []
    while num > 0:
        num, d = divmod(num, len(B36))
        s.append(B36[d])
    return "".join(reversed(s)) or B36[0]

RENAME_RE = re.compile(r'Reference-Manual([0-9]+)\.html')
def rename_sub(match):
    num = int(match.groups(1)[0])
    return b36(num) + ".html"

MIN_DIR = "min"

def compress_attributes(soup):
    for span in soup.find_all('span'):
        style = span['style']
        if style == "font-style:italic" or style == "font-style:oblique":
            span.name = 'i'
        elif style == "font-family:monospace":
            span.name = 'tt'
        elif style == 'font-weight:bold':
            span.name = 'b'
        elif style == 'font-size:small':
            span.name = 'small'
        # elif style == 'font-family:sans-serif':
            # span.name = 'u'
        else:
            # print(style) font-family:sans-serif
            continue
        span.attrs = {}

def fixup(path):
    if path.endswith(".min.html"):
        return

    with open(path, mode='rb') as html_file:
        soup = BeautifulSoup(html_file)

    compress_attributes(soup)

    _, fname = split(path)
    html_out = join(MIN_DIR, RENAME_RE.sub(rename_sub, fname))

    with open(html_out, mode='w') as html_output:
        html_output.write(RENAME_RE.sub(rename_sub, str(soup)))

    # if RENAME_RE.match(fname):
    #     min_out = html_out + ".min"
    #     with open(min_out, mode='wb') as min_output:
    #         call(["html-minifier", "--remove-comments", "--collapse-whitespace",
    #               "--remove-attribute-quotes", "--collapse-boolean-attributes",
    #               "--remove-redundant-attributes", "--use-short-doctype",
    #               "--remove-optional-tags", "--remove-empty-elements", html_out], stdout=min_output)
    #     rename(min_out, html_out)

def main(paths):
    for path in paths:
        fixup(path)

try:
    mkdir(MIN_DIR)
except OSError as exception:
    if exception.errno != errno.EEXIST:
        raise

main(sys.argv[1:]) #["/build/coq/doc/refman/html/Reference-Manual142.html"]) #sys.argv[1:])
