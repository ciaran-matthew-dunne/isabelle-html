# TODO: 
# ∙ Add support for definitions where the fact different to the name
#   given after the 'where' keyword
# ∙ Add support for definition names in quotes

import xml.etree.ElementTree as etree

### Preparing stuff
gzf_path = "../out/html/Unsorted/GZF-HOL/Model_locale.html"
gzf_tree = etree.parse(gzf_path)
gzf_root = gzf_tree.getroot()
spans = gzf_root[1][1]


tmapI = [(spans[n],n) for n in range(180,186)]
disjI = [(spans[n],n) for n in range(344,359)]
tier_set = [(spans[n],n) for n in range(897,920)]

def printe(elem):
  if elem.text:
    print("tx:" + elem.text)
  if elem.tail:
    print("tl:" + elem.tail)
  if elem.attrib:
    print("att:" + str(elem.attrib))  

def printsp(n,m):
  for i in range(n,m):
    if spans[i].text or spans[i].tail:
      print("#" + str(i))
      printe(spans[i])

def printspl(l):
  for (elem,n) in l:
    if elem.text or elem.tail:
      print("#" + str(n))
      printe(elem)             

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
    if name not in [None, "\""]:
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
  elem.set('class','unlinked-fact')
  elem.text = name
  return elem

def add_spaces(xs):
  intersperse = (lambda xs, e: [e] + [b for ys in [[a,e] for a in xs] for b in ys])
  blank = etree.Element('html:a')
  blank.text = ' '
  return intersperse(xs, blank)

def fact_split(str):
  if str == '': 
    return []
  if str[0] in ['\n', ' ']:
    i = 1
    hd = str[0]  
    while str[i:] and str[i] in ['\n', ' ']:
      hd += str[i]
      i += 1
    return [hd] + fact_split(str[i:]) 
  else:
    i = 1
    hd = str[0]  
    while str[i:] and str[i] not in ['\n', ' ']:
      hd += str[i]
      i += 1
    return [hd] + fact_split(str[i:]) 

def add_elem_links(elem, fact_bank, thy, path):
  items = fact_split(elem.tail)
  elem.tail = ''
  elem.extend([fact_link(name, thy, path)\
      if name in fact_bank else fact_obj(name)\
      for name in facts])

# def get_thm_ranges(spans):
#   using_inds = decl_inds(spans, "from")\
#              + decl_inds(spans, "with")\
#              + decl_inds(spans, "using")\
#              + decl_inds(spans, "unfolding")
#   for n in using_inds:
#     m = n
#     while spans[m].attrib != 'keyword1':

# After which keywords can facts be mentioned?
# - using, from, with, unfolding
# - note, thm
# - simp add:|only:, auto|blast intro:|elim:, 
# - unfold, rule, induct, subst, insert, cases, OF, THEN


def insert_links(spans, fact_bank, thy, path):
  # Insert links to declarations, avoiding binding occurrences
  # If 'name_def' is the tail of a span such that span.text=='where',
  # then it is a binding occurrence  s
  using_inds = decl_inds(spans, "from")\
             + decl_inds(spans, "with")\
             + decl_inds(spans, "using")\
             + decl_inds(spans, "unfolding")
  for n in using_inds:
    elem = spans[n]
    if elem.tail not in [None, '']:
      if has_OF(n):
        facts = gather_facts(spans,n)
      else:   
        facts = elem.tail.split()
        elem.tail = ''
        fact_elems = add_spaces([fact_link(name, thy, path)\
                               if name in fact_bank else fact_obj(name)\
                               for name in facts])
        elem.extend(fact_elems)
  rule_inds = decl_inds(spans, "rule")
  # for elem in [spans[n] for n in rule_inds]:
  # if elem.tail not in [None, '']:
  #   facts = elem.tail.split()
  #   elem.tail = ''
  #   fact_elems = add_spaces([fact_link(name, thy, path)\
  #                          if name in fact_bank else fact_obj(name)\
  #                          for name in facts])


def link_html():
  facts = get_thm_names(spans, "Model_locale") + get_def_names(spans, "Model_locale")
  insert_links(spans, facts, "Model_locale", gzf_path)
  f = open("../out/test/Model.xml",'wb')
  gzf_tree.write(f, method='html')
  f.close()
# When elem.text == lemma, let lem_name := elem.tail
# We add the extra key 'id' with value 'GZF_locale.GBL.lem_name' 

# Occurences of facts need to be replaced with  
# <a class="pst-link" 
#    href="http://www.macs.hw.ac.uk/~cmd1/IsabelleGZF/GZF_locale.html#GZF_locale.GBL.fact_name">
#  fact_name  
# </a>
