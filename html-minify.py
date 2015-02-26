import re
import sys
import errno
from os import mkdir
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

    for i in soup.find_all('i'):
        right = i.next_sibling
        if right and right.name == 'sub':
            for child in right.children:
                if child.name != 'i':
                    child.wrap(soup.new_tag('i'))

    # for tt in soup.find_all('tt'):
    #     for ti in tt.find_all('i'):
    #         ti.name = 'ti'

def fixup(path, outdir):
    if path.endswith(".min.html"):
        return

    with open(path, mode='rb') as html_file:
        soup = BeautifulSoup(html_file)

    compress_attributes(soup)

    _, fname = split(path)
    html_out = join(outdir, RENAME_RE.sub(rename_sub, fname))

    with open(html_out, mode='w') as html_output:
        html_output.write(RENAME_RE.sub(rename_sub, str(soup)))

def main(paths, outdir):
    try:
        mkdir(outdir)
    except OSError as exception:
        if exception.errno != errno.EEXIST:
            raise

    for path in paths:
        fixup(path, outdir)

main(sys.argv[2:], sys.argv[1])
