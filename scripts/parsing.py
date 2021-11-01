# TODO: 
# ∙ Add support for definitions where the fact different to the name
#   given after the 'where' keyword
# ∙ Add support for definition names in quotes
from lxml import etree as etree
import os
import subprocess

## DEBUGGING STUFF:
gzf_path = "../out/html/Unsorted/GZF-HOL/Model_locale.html"
gzf_tree = etree.parse(gzf_path)
gzf_root = gzf_tree.getroot()
spans = gzf_root[1][1]
theories = ['ML_Bootstrap', 'Pure', 'Sessions', 'Code_Generator', 'ATP', 'Archimedean_Field', 'Argo', 'BNF_Cardinal_Arithmetic', 'BNF_Cardinal_Order_Relation', 'BNF_Composition', 'BNF_Def', 'BNF_Fixpoint_Base', 'BNF_Greatest_Fixpoint', 'BNF_Least_Fixpoint', 'BNF_Wellorder_Constructions', 'BNF_Wellorder_Embedding', 'BNF_Wellorder_Relation', 'Basic_BNF_LFPs', 'Basic_BNFs', 'Binomial', 'Code_Evaluation', 'Code_Numeral', 'Complete_Lattices', 'Complete_Partial_Order', 'Complex', 'Complex_Main', 'Conditionally_Complete_Lattices', 'Ctr_Sugar', 'Deriv', 'Divides', 'Enum', 'Equiv_Relations', 'Euclidean_Division', 'Extraction', 'Factorial', 'Fields', 'Filter', 'Finite_Set', 'Fun', 'Fun_Def', 'Fun_Def_Base', 'GCD', 'Groebner_Basis', 'Groups', 'Groups_Big', 'Groups_List', 'HOL', 'Hilbert_Choice', 'Hull', 'Inductive', 'Inequalities', 'Int', 'Lattices', 'Lattices_Big', 'Lazy_Sequence', 'Lifting', 'Lifting_Set', 'Limited_Sequence', 'Limits', 'List', 'MacLaurin', 'Main', 'Map', 'Meson', 'Metis', 'Modules', 'Nat', 'Nitpick', 'NthRoot', 'Num', 'Numeral_Simprocs', 'Nunchaku', 'Option', 'Order_Relation', 'Orderings', 'Parity', 'Partial_Function', 'Power', 'Predicate', 'Predicate_Compile', 'Presburger', 'Product_Type', 'Quickcheck_Exhaustive', 'Quickcheck_Narrowing', 'Quickcheck_Random', 'Quotient', 'Random', 'Random_Pred', 'Random_Sequence', 'Rat', 'Real', 'Real_Vector_Spaces', 'Record', 'Relation', 'Rings', 'SAT', 'SMT', 'Semiring_Normalization', 'Series', 'Set', 'Set_Interval', 'Sledgehammer', 'String', 'Sum_Type', 'Topological_Spaces', 'Transcendental', 'Transfer', 'Transitive_Closure', 'Typedef', 'Typerep', 'Vector_Spaces', 'Wellfounded', 'Wfrec', 'Zorn', 'Code_Generator', 'Connection_locale', 'GZF_locale', 'Model_locale', 'Ord_locale']

tmapI = [(spans[n],n) for n in range(180,186)]
disjI = [(spans[n],n) for n in range(344,359)]
tier_set = [(spans[n],n) for n in range(911,930)]

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


### Preparing stuff
parser = etree.XMLParser(encoding="utf-8")
chapter = 'Unsorted'
session = 'GZF-HOL'
root_dir = "../tsrc/"
html_path = os.path.abspath('../out/html/')
out_path  = os.path.abspath("../out/test/")
root_path = os.path.abspath(root_dir)

## Building HTML of session and dependencies
def build_html():
  sessions_cmd = "isabelle sessions -D " + root_path
  tmp = b'Pure\nTools\nHOL\nGZF-HOL\n'
  session_stdout = tmp.decode("utf-8")
  # subprocess.run(sessions_cmd, shell=True, capture_output=True).stdout.decode("utf8")
  all_sessions = ' '.join(list(filter(None, session_stdout.split('\n'))))
  option = '-o quick_and_dirty'
  build_cmd = "isabelle env\
    ISABELLE_BROWSER_INFO=" + html_path +\
    " isabelle build " + option + " -d " + root_path +\
    " -c -o browser_info " + all_sessions

## Getting names of theories in session dependencies
def get_thys(session):
  files_cmd = "isabelle build -n -l -d " + root_path + " " + session
  files_stdout = subprocess.run(files_cmd, shell=True, capture_output=True)\
                           .stdout.decode("utf8").split('\n')
  return [ line.rsplit(os.sep, 1)[1].rsplit('.',1)[0] for line in files_stdout\
            if line[-4:] == '.thy']

def get_html_paths(thys):
  html_paths = []
  for subdir, dirs, files in os.walk(html_path):
    for filename in files:
      if filename[-5:] == '.html'\
      and filename[-8:-5] != '.ML'\
      and filename[:-5] in thys:
        html_paths.append(subdir + os.sep + filename)
  return html_paths

### Parsing names of declarations
def is_decl(elem, decl_name):
  items = list(elem.itertext())
  return decl_name in items

def decl_inds(spans, decl_name):  
  return [ n for n in range(len(spans)) if is_decl(spans[n], decl_name)]

# Traverses tree and creates hooks for each theorem/definition,
# returning a list of each definition name.
def hook_and_get_thm_names(spans):
  n = 0; thm_names = []
  while n in range(len(spans)):
    if spans[n][0:]:
      if spans[n][0].text in ['lemma','theorem','corollary',\
                             'proposition','lemmas','named_theorems']:
        elem = spans[n]
        name = elem.tail.strip()
        thm_names.append(name)
        elem.set('id',  name)
      elif spans[n][0].text == 'definition':
        elem = spans[n+1]
        name = elem.text
        if name not in [None, "\""]:
          thm_names.append(name + "_def")
          elem.set('id', name + "_def")      
    n += 1                             
  return list(filter(None,thm_names))

def hook_and_gen_library(html_files):
  fact_library = []
  for file in html_files:
    print(file)
    html_tree = etree.parse(file,parser=etree.XMLParser(encoding='utf-8',recover=True))
    html_root = html_tree.getroot()
    spans = html_root[1][1]
    thms = hook_and_get_thm_names(spans)
    fact_library.append((file,html_tree,thms))
  return fact_library  

#### Inserting links to facts
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

def fact_link(name, thy, path):
  elem = etree.Element('html:a')
  elem.set('class','pst-link')
  elem.set('href', path + "#" + thy + "." + name)
  elem.text = name
  return elem

def text_elem(name):
  elem = etree.Element('html:a')
  elem.set('class','pad')
  elem.text = name
  return elem

def add_elem_links(elem, fact_bank, thy, path):
  items = fact_split(elem.tail)
  elem.tail = ''
  elem.extend([fact_link(txt, thy, path)\
      if txt in fact_bank else text_elem(txt)\
      for txt in items])

## TODO: link facts invoked by 'note' and 'thm' and 'declare'
def thm_links(spans, fact_bank, thy, path):
  i = 0 
  while i in range(len(spans)):
    ## Keyword case:
    if spans[i][0:] and spans[i][0].text in ['from','with','using','unfolding']:
      j = i
      while (spans[j:]) and (i == j or\
        not (spans[j].get("class") in ['keyword1', 'keyword3'])):
        tl = spans[j].tail
        if tl and tl.strip() != '':
          add_elem_links(spans[j], fact_bank, thy, path)
        j += 1  
    ## Quasi-keyword case
    if spans[i].text in ['rule','use','unfold','fact']\
    or spans[i].get("class") == 'quasi_keyword':
      j = i
      while (spans[j:]) and (i == j or\
        not (spans[j].text == ')'\
         or spans[j].get("class") in ['quasi_keyword','keyword2']\
         or (spans[j][0:] and spans[j][0].text == ','))):
        tl = spans[j].tail
        if tl and tl.strip() != '':
          add_elem_links(spans[j], fact_bank, thy, path)
        j += 1  
    i += 1     

def link_html(path, out_dir):
  thy = path.split('/')[-1].split('.')[0]
  out_file = out_dir + "/" + thy + ".xml"
  facts = get_thm_names(spans, thy) + get_def_names(spans, thy)
  thm_links(spans, facts, thy, out_file)
  f = open(out_file, 'wb')
  gzf_tree.write(f, method='html')
  f.close()
