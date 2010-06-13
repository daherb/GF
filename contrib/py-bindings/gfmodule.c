#include <Python.h>
#include "pgf.h"

#define NEWOBJECT(OBJ, GFTYPE) typedef struct {\
  PyObject_HEAD \
  GFTYPE obj; \
} OBJ;
#define NEWTYPE(TYPE,NAME,OBJECT,DOC) static PyTypeObject TYPE = {\
  PyObject_HEAD_INIT(NULL)\
  0,                         /*ob_size*/\
  NAME,             /*tp_name*/\
  sizeof(OBJECT), /*tp_basicsize*/\
  0,                         /*tp_itemsize*/\
  0,                         /*tp_dealloc*/\
  0,                         /*tp_print*/\
  0,                         /*tp_getattr*/\
  0,                         /*tp_setattr*/\
  0,                         /*tp_compare*/\
  0,                         /*tp_repr*/\
  0,                         /*tp_as_number*/\
  0,                         /*tp_as_sequence*/\
  0,                         /*tp_as_mapping*/\
  0,                         /*tp_hash */\
  0,                         /*tp_call*/\
  0,                         /*tp_str*/\
  0,                         /*tp_getattro*/\
  0,                         /*tp_setattro*/\
  0,                         /*tp_as_buffer*/\
  Py_TPFLAGS_DEFAULT,        /*tp_flags*/\
  DOC,           /* tp_doc */\
};
#define NEWGF(OBJ,GFTYPE,TYPE,NAME,DOC) NEWOBJECT(OBJ,GFTYPE)	\
NEWTYPE(TYPE,NAME,OBJ,DOC)

#define DEALLOCFN(delname,t,cb,cbname) static void \
delname(t *self){ cb(self->obj);\
	printf("gf_%s has been called for stable pointer 0x%x\n", cbname, self->obj);\
	self->ob_type->tp_free((PyObject*)self); }

#define REPRCB(cbid,t,gfcb) static PyObject* \
cbid(t *self) { \
	const char *str = gfcb(self->obj); \
 	return PyString_FromFormat("0x%x: %s", self->obj, str); }

/* utilities */

int
checkType(PyObject* obj, PyTypeObject* tp)
{
	int isRight = PyObject_TypeCheck(obj, tp);
	if (!isRight)
		PyErr_Format(PyExc_TypeError, "Expected a %s", tp->tp_doc);
	return isRight;
}


/* new types and declarations */

NEWGF(Lang,GF_Language,LangType,"gf.lang","language")
NEWGF(gfType,GF_Type,gfTypeType,"gf.type","gf type")
NEWGF(PGFModule,GF_PGF,PGFType,"gf.pgf","PGF module")
NEWGF(Expr,GF_Expr,ExprType,"gf.expr","gf expression")	
NEWGF(Tree,GF_Tree,TreeType,"gf.tree","gf tree")


/* PGF methods, constructor and destructor */

DEALLOCFN(PGF_dealloc, PGFModule, gf_freePGF, "freePGF")

static gfType*
startCategory(PyObject *self, PyObject *noarg)
{
  gfType *cat;
  if (!checkType(self, &PGFType)) return NULL;
  cat = (gfType*)gfTypeType.tp_new(&gfTypeType,NULL,NULL);
  cat->obj = gf_startCat(((PGFModule*)self)->obj);
  return cat;
}

static PyObject*
parse(PyObject *self, PyObject *args, PyObject *kws)
{
	PyObject *lang_pyob, *cat_pyob = NULL;
	GF_PGF pgf;
	GF_Language lang;
	GF_Type cat;
	char *lexed;
	static char *kwlist[] = {"lexed", "lang", "cat", NULL};
	if (!PyArg_ParseTupleAndKeywords(args, kws, "sO|O", kwlist,
									&lexed, &lang_pyob, &cat_pyob))
    	return NULL;
	if (!checkType(self, &PGFType)) return NULL;	
	if (!checkType(lang_pyob, &LangType)) return NULL;
	if (cat_pyob) {
		if (!checkType(cat_pyob, &gfTypeType)) return NULL;
		cat = ((gfType*)cat_pyob)->obj;
	} else { 
		cat = startCategory(self,NULL)->obj;		
	} 
	pgf = ((PGFModule*)self)->obj;
	lang = ((Lang*)lang_pyob)->obj;
	PyObject *parsed = PyList_New(0);
	GF_Tree *p = gf_parse(pgf,lang,cat,lexed); 
	if (*p) {
    	do {
			Tree* expr; //Expr
			expr = (Tree*)TreeType.tp_new(&TreeType,NULL,NULL); // Expr* -> Tree*
			expr->obj = *(p++);
      		PyList_Append(parsed, (PyObject*)expr);
			Py_DECREF(expr); //??
      /*      char *str = gf_showExpr(exp);
      puts(str);
      free(str); */
    	} while (*p);
  	}
  return parsed;
}

static PGFModule*
readPGF(PyObject *self, PyObject *args)
{
  char *path;
  PGFModule *pgf;
  if (!PyArg_ParseTuple(args, "s", &path))
    return NULL;
  pgf = (PGFModule*)PGFType.tp_new(&PGFType,NULL,NULL);
  if (!pgf) return NULL;
  pgf->obj = gf_readPGF(path);
  return pgf;
}

//Todo: repr

static PyMethodDef pgf_methods[] = {
  {"parse", (PyCFunction)parse, METH_VARARGS|METH_KEYWORDS,"Parse a string."},
  {"startcat", (PyCFunction)startCategory, METH_NOARGS,"Get the start category."},
  {NULL, NULL, 0, NULL}  /* Sentinel */
};




/* Language methods, constructor and destructor */

REPRCB(lang_repr, Lang, gf_showLanguage)
DEALLOCFN(Lang_dealloc, Lang, gf_freeLanguage, "freeLanguage")

static Lang*
readLang(PyObject *self, PyObject *args)
{
  char *langName;
  Lang *l;
  if (!PyArg_ParseTuple(args,"s",&langName))
    return NULL;
  l = (Lang*)LangType.tp_new(&LangType,NULL,NULL);
  if(!l) return NULL;
  l->obj = gf_readLanguage(langName);
  return l;
}



/* gf types: methods, constructor and destructor */

DEALLOCFN(gfType_dealloc, gfType, gf_freeType, "freeType")
REPRCB(gfType_repr, gfType, gf_showType)




/* expression type: methods, destructor */

DEALLOCFN(expr_dealloc, Expr, gf_freeExpr, "freeExpr")
REPRCB(expr_repr, Expr, gf_showExpr)


/* tree typr: methods, constructor and destructor */
//  Are Expr and Tree equivalent ? 

REPRCB(tree_repr, Tree, gf_showExpr)
DEALLOCFN(Tree_dealloc, Tree, gf_freeTree, "freeTree")


/* gf module methods */

static PyMethodDef gf_methods[] = {
  {"read_pgf", (PyCFunction)readPGF, METH_VARARGS,"Read pgf file."},
  {"read_language", (PyCFunction)readLang, METH_VARARGS,"Get the language."},
  {"startcat", (PyCFunction)startCategory, METH_VARARGS,"Get the start category of a pgf module."},
  {NULL, NULL, 0, NULL}  /* Sentinel */
};


#ifndef PyMODINIT_FUNC/* declarations for DLL import/export */
#define PyMODINIT_FUNC void
#endif

PyMODINIT_FUNC
initgf(void) 
{
  PyObject* m;
#define READYTYPE(t,trepr,tdealloc) t.tp_new = PyType_GenericNew; \
    t.tp_repr = (reprfunc)trepr; \
	t.tp_dealloc = (destructor)tdealloc; \
	if (PyType_Ready(&t) < 0) return;
	
	PGFType.tp_methods = pgf_methods;
	READYTYPE(PGFType,NULL,PGF_dealloc)
	READYTYPE(LangType, lang_repr, Lang_dealloc)
	READYTYPE(gfTypeType, gfType_repr, gfType_dealloc)
	READYTYPE(ExprType, expr_repr, expr_dealloc)
	READYTYPE(TreeType, tree_repr, Tree_dealloc)	

  m = Py_InitModule3("gf", gf_methods,
		     "Grammatical Framework.");
  static char *argv[] = {"gf.so", 0}, **argv_ = argv;
  static int argc = 1;
  gf_init (&argc, &argv_);
  hs_add_root (__stginit_PGFFFI);

#define ADDTYPE(t) Py_INCREF(&t);\
PyModule_AddObject(m, "gf", (PyObject *)&t);

	ADDTYPE(PGFType)
	ADDTYPE(LangType)
	ADDTYPE(gfTypeType)
	ADDTYPE(TreeType)
	ADDTYPE(ExprType)
}
