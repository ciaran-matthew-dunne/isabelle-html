# TODO: 
# ∙ Add support for definitions where the fact different to the name
#   given after the 'where' keyword
# ∙ Add support for definition names in quotes

import xml.etree.ElementTree as etree
from itertools import chain, izip, repeat, islice

### Preparing stuff
gzf_path = "../out/Unsorted/GZF-HOL/GZF_locale.html"
gzf_tree = etree.parse(gzf_path)
gzf_root = gzf_tree.getroot()
spans = gzf_root[1][1]

### Parsing names of declarations
def is_decl(elem, decl_name):
  items = list(elem.itertext())
  return decl_name in items

def decl_inds(spans, decl_name):  
  return [ n for n in range(len(spans)) if is_decl(spans[n], decl_name)]

# Traverses tree and creates hooks for each definition,
# returning a list of each definition name. 
def get_def_names(spans, thy):
  def_inds = decl_inds(spans, "definition")
  def_names = []
  for n in def_inds:
    elem = spans[n+1]
    name = elem.text
    if name !="\"":
      def_names.append(name + "_def")
      elem.set('id', thy + '.' + name + "_def")
  return def_names

def get_thm_names(spans,thy):
  thm_inds = decl_inds(spans, "lemma") \
          + decl_inds(spans, "theorem") \
          + decl_inds(spans, "corollary") \
          + decl_inds(spans, "proposition") \
          + decl_inds(spans, "lemmas") \
          + decl_inds(spans, "named_theorems")
  thm_names = []
  for n in thm_inds:
    elem = spans[n]
    name = elem.tail.strip()
    thm_names.append(name)
    elem.set('id', thy + '.' + name)
  return thm_names

#### Inserting links to facts
def fact_link(name, thy, path):
  elem = etree.Element('html:a')
  elem.set('class','pst-link')
  elem.set('href', path + "#" + thy + "." + name)
  elem.text = name
  return elem

def fact_obj(name):
  elem = etree.Element('html:a')
  elem.text = name
  return elem
# After which keywords can facts be mentioned?
# - using, from, with, unfolding
# - note, thm
# - simp add:|only:, auto|blast intro:|elim:, 
# - unfold, rule, induct, subst, insert, cases, OF, THEN
def pad_list(seq):
    blank_elem = etree.Element('a')
    blank_elem.text = ' '
    return [blank_elem] +\
      list(islice(chain.from_iterable(izip(repeat(blank_elem), seq)), 1, None))\
      + [blank_elem]

def insert_links(spans, fact_bank, thy, path):
  # Insert links to declarations, avoiding binding occurrences
  # If 'name_def' is the tail of a span such that span.text=='where',
  # then it is a binding occurrence  
  using_inds = decl_inds(spans, "using")
  for n in using_inds:
    elem = spans[n]
    facts = elem.tail.split()
    elem.tail = ''
    fact_elems = pad_list([fact_link(name, thy, path)\
                           if name in fact_bank else fact_obj(name)\
                           for name in facts])
    elem.extend(fact_elems)

def link_html():
  facts = get_thm_names(spans, "GZF_locale") + get_def_names(spans, "GZF_locale")
  insert_links(spans, facts, "GZF_locale", gzf_path)
  f = open("../out/test/tes2t.xml",'w')
  gzf_tree.write(f, method='html')
  f.close()
# When elem.text == lemma, let lem_name := elem.tail
# We add the extra key 'id' with value 'GZF_locale.GBL.lem_name' 

# Occurences of facts need to be replaced with  
# <a class="pst-link" 
#    href="http://www.macs.hw.ac.uk/~cmd1/IsabelleGZF/GZF_locale.html#GZF_locale.GBL.fact_name">
#  fact_name  
# </a>
