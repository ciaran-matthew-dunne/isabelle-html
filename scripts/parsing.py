import xml.etree.ElementTree as ET
import lxml.etree as etree 

gzf_path = "../out/Unsorted/GZF-HOL/GZF_locale.html"
gzf_tree = etree.parse(gzf_path)
gzf_root = gzf_tree.getroot()
spans = list(gzf_root[1][1])	


def is_decl(elem, decl_name):
	items = list(elem.itertext())
	return decl_name in items

def get_ind(spans, decl_name):	
	return [ n for n in range(len(spans)) if is_decl(spans[n], decl_name)]

def get_ind_using(spans, decl_name):	
	return [ n for n in range(len(spans)) if is_decl(spans[n], "")]

def get_defs(spans):	
	defs = [ spans[n+1].text for n in get_ind(spans, "definition")]
	
	# Sometimes names can be surrounded by quotes,
	# currently we just remove them.
	defs = list(filter(lambda str: str!="\"",defs))

	# Sometimes the name of the fact is given seperately,
	# currently we don't do anything with them.
	return defs	

def get_lemmas(spans):
	return [ spans[n].tail.strip() for n in get_ind(spans, "lemma") ]	

def insert_links(spans, facts):
	for elem in spans:
		if elem.tail!=None:
			for lem in elem.tail.split():
				if lem in facts: 
					link()

lemmas = get_lemmas(spans)

# In the same element that a definition name is at,
# we need to add a new key 'id' with value 'GZF_locale.GBL.def_name'

# When elem.text == lemma, let lem_name := elem.tail
# We add the extra key 'id' with value 'GZF_locale.GBL.lem_name' 

# Occurences of facts need to be replaced with  
# <a class="pst-link" 
#    href="http://www.macs.hw.ac.uk/~cmd1/IsabelleGZF/GZF_locale.html#GZF_locale.GBL.fact_name">
#  fact_name	
# </a>
