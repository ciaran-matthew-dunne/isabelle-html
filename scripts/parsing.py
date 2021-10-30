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

def text_elem(name):
  elem = etree.Element('html:a')
  elem.set('class','unlinked-fact')
  elem.text = name
  return elem

def fact_split(str):
  if str == '': 
    return []
  i = 1
  hd = str[0]  
  if str[0] in ['\n', ' ']:
    while str[i:] and str[i] in ['\n', ' ']:
      hd += str[i]
      i += 1
    return [hd] + fact_split(str[i:]) 
  else:
    while str[i:] and str[i] not in ['\n', ' ']:
      hd += str[i]
      i += 1
    return [hd] + fact_split(str[i:]) 

def add_elem_links(elem, fact_bank, thy, path):
  items = fact_split(elem.tail)
  elem.tail = ''
  elem.extend([fact_link(txt, thy, path)\
      if txt in fact_bank else text_elem(txt)\
      for txt in items])

def insert_keyword_thm_links(spans, fact_bank, thy, path):
  keyword_inds = decl_inds(spans, "from")\
             + decl_inds(spans, "with")\
             + decl_inds(spans, "using")\
             + decl_inds(spans, "unfolding")
  for n in keyword_inds:
    m = n
    print("n=" + str(n))
    while (spans[m:]) and (m == n or spans[m].get("class") not in ['keyword1', 'keyword3']):
      tl = spans[m].tail
      if tl and tl.strip() != '':
        add_elem_links(spans[m], fact_bank, thy, path)
      m += 1  
    print("m="+ str(m))  


# After which keywords can facts be mentioned?
# - using, from, with, unfolding
# - note, thm
# - simp add:|only:, auto|blast intro:|elim:, 
# - unfold, rule, induct, subst, insert, cases, OF, THEN

def link_html():
  facts = get_thm_names(spans, "Model_locale") + get_def_names(spans, "Model_locale")
  insert_keyword_thm_links(spans, facts, "Model_locale", gzf_path)
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
