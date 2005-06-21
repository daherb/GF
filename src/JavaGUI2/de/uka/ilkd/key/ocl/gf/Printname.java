package de.uka.ilkd.key.ocl.gf;

import java.util.Hashtable;
import java.util.Vector;

import org.apache.log4j.Logger;

/**
 * @author daniels
 *
 * A Printname allows easy access for all the information that is crammed
 * into a printname in the GF grammars.
 * This information consists of (in this order!)
 *   The tooltip text which is started with $
 * 	 The subcategory which is started with %
 *   The longer explanation for the subcategory which directly follows the
 *     subcategory and is put into parantheses
 *   The parameter descriptions, which start with #name and is followed
 *     by their actual description.
 * HTML can be used inside the descriptions and the tooltip text 
 */
class Printname {
        protected static Logger subcatLogger = Logger.getLogger(Printname.class.getName());
        
        public static final Printname delete = new Printname("d", "delete current sub-tree");
        public static final Printname addclip = new Printname("ac", "add to clipboard\\$<html>adds the current subtree to the clipboard.<br>It is offered in the refinement menu if the expected type fits to the one of the current sub-tree.</html>");
        public static final Printname printhistory = new Printname("ph", "print history\\$prints all previous command in the linearization area");

        /** 
         * The character that is the borderline between the text that
         * is to be displayed in the JList and the ToolTip text
         */
        public final static String TT_START = "\\$";
        /** 
         * the string that is followed by the sub-category shorthand
         * in the refinement menu
         */ 
        public final static String SUBCAT = "\\%";
        /**
         * The string that is followed by a new parameter to the GF function
         */
        public final static String PARAM = "\\#";
        
        
        /** the name of the fun that is used in this command */
        protected final String fun;

        /** the printname of this function */
        protected final String printname;
        
        /** to cache the printname, once it is constructed */
        protected String displayedPrintname = null;
        
        
        /** 
         * the name of the module the fun belongs to
         * null means that the function is saved without module information,
         * "" means that a GF command is represented
         */
        protected final String module;
        /** 
         * the name of the module the fun belongs to
         * null means that the function is saved without module information,
         * "" means that a GF command is represented
         */
        public String getModule() {
                return module;
        }
        
        
        /** the qualified function name, not needed yet */
        /*
        public String getFunQualified() {
                if (module != null && !module.equals("")) {
                        return module + "." + fun;
                } else {
                        return fun;
                }
        }
        */
        
        /** the subcategory of this command */
        protected final String subcat;
        /** the subcategory of this command */
        public String getSubcat() {
                return subcat;
        }

        /**
         * The hashmap for the names of the sub categories, 
         * with the shortname starting with '%' as the key.
         * It is important that all Printnames of one session share the same
         * instance of Hashtable here. 
         * This field is not static because there can be several instances of
         * the editor that shouldn't interfere.
         */
        protected final Hashtable subcatNameHashtable;

        /**
         * contains the names of the paramters of this function (String).
         * Parallel with paramTexts
         */
        protected final Vector paramNames = new Vector();
        
        /**
         * fetches the name of the nth parameter
         * @param n the number of the wanted paramter
         * @return the corresponding name, null if not found
         */
        public String getParamName(int n) {
                String name = null;
                try {
                name = (String)this.paramNames.get(n);
                } catch (ArrayIndexOutOfBoundsException e) {
                        subcatLogger.warn(e.getLocalizedMessage());
                }
                return name;
        }
        /**
         * contains the descriptions of the paramters of this function (String).
         * Parallel with paramNames
         */
        protected final Vector paramTexts = new Vector();

        
        /**
         * Creates a Printname for a normal GF function
         * @param myFun the function name
         * @param myPrintname the printname given for this function
         * @param myFullnames the Hashtable for the full names for the category
         * names for the shortnames like %PREDEF
         */
        public Printname(String myFun, String myPrintname, Hashtable myFullnames) {
                myFun = myFun.trim();
                myPrintname = myPrintname.trim();
                this.printname = myPrintname;
                this.subcatNameHashtable = myFullnames;

                //parse the fun name
                {
                int index = myFun.indexOf('.');
                if (index > -1) {
                        //a valid fun name must not be empty
                        this.fun = myFun.substring(index + 1);
                        this.module = myFun.substring(0, index);
                } else {
                        this.fun = myFun;
                        this.module = null;
                }
                }
                
                //parse the parameters and cut that part
                {
                int index = Utils.indexOfNotEscaped(myPrintname, PARAM);
                if (index > -1) {
                        String paramPart = myPrintname.substring(index);
                        String splitString;
                        //split takes a regexp as an argument. So we have to escape the '\' again.
                        if (PARAM.startsWith("\\")) {
                                splitString = "\\" + PARAM;
                        } else {
                                splitString = PARAM;
                        }
                        String[] params = paramPart.split(splitString);
                        //don't use the first split part, since it's empty
                        for (int i = 1; i < params.length; i++) {
                                String current = params[i];
                                int nameEnd = current.indexOf(' ');
                                int nameEnd2 = Utils.indexOfNotEscaped(current, PARAM);
                                if (nameEnd == -1) {
                                        nameEnd = current.length();
                                }
                                String name = current.substring(0, nameEnd);
                                String description;
                                if (nameEnd < current.length() - 1) {
                                        description = current.substring(nameEnd + 1).trim();
                                } else {
                                        description = "";
                                }
                                this.paramNames.addElement(name);
                                this.paramTexts.addElement(description);
                        }
                        myPrintname = myPrintname.substring(0, index);
                }
                }
                
                
                //extract the subcategory part and cut that part
                {
                int index = Utils.indexOfNotEscaped(myPrintname, SUBCAT);
                if (index > -1) {
                        String subcatPart = myPrintname.substring(index);
                        myPrintname = myPrintname.substring(0, index);
                        int indFull = subcatPart.indexOf('{');
                        if (indFull > -1) {
                                int indFullEnd = subcatPart.indexOf('}', indFull + 1);
                                if (indFullEnd == -1) {
                                        indFullEnd = subcatPart.length();
                                }
                                String fullName = subcatPart.substring(indFull + 1, indFullEnd);
                                this.subcat = subcatPart.substring(0, indFull).trim();
                                this.subcatNameHashtable.put(this.subcat, fullName);
                                if (subcatLogger.isDebugEnabled()) {
                                        subcatLogger.debug("new fullname '" + fullName + "' for category (shortname) '" + this.subcat + "'");
                                }
                        } else {
                                subcat = subcatPart.trim();
                        }
                        
                } else {
                        this.subcat = null; 
                }
                }
        }

        /**
         * a constructor for GF command that don't represent functions,
         * like d, ph, ac
         * @param command the GF command
         * @param explanation an explanatory text what this command does
         */
        protected Printname(String command, String explanation) {
                this.fun = command;
                this.subcatNameHashtable = null;
                this.subcat = null;
                this.module = "";
                this.printname = explanation;
        }
        
        /**
         * Special constructor for bound variables.
         * These printnames don't get saved since they don't always exist and
         * also consist of quite few information.
         * @param bound The name of the bound variable
         */
        public Printname(String bound) {
                this.fun = bound;
                this.subcatNameHashtable =  null;
                this.subcat = null;
                this.module = null;
                this.printname = bound + "$insert the bound variable" + bound;
        }
        
        /** the text that is to be displayed in the refinement lists */
        public String getDisplayText() {
                String result;
                result = extractDisplayText(this.printname);
                return result;
        }

        /**
         * the text that is to be displayed as the tooltip.
         * Will always be enclosed in &lt;html&gt; &lt;/html&gt; tags.
         */
        public String getTooltipText() {
                if (this.displayedPrintname != null) {
                        return this.displayedPrintname;
                } else {
	                String result;
	                result = extractTooltipText(this.printname);
	                if (this.paramNames.size() > 0) {
	                        String params = htmlifyParams();
	                        //will result in <html> wrapping
	                        result = htmlAppend(result, params);
	                } else {
	                        //wrap in <html> by force
	                        result = htmlAppend(result, "");
	                }
	                this.displayedPrintname = result;
	                return result;
                }
        }

        /**
         * extracts the part of the body of the printname that is the tooltip
         * @param myPrintname the body of the printname
         * @return the tooltip
         */
        public static String extractTooltipText(String myPrintname) {
                //if the description part of the fun has no \$ to denote a tooltip,
                //but the subcat description has one, than we must take extra
                //caution
                final int indTT = Utils.indexOfNotEscaped(myPrintname, TT_START);
                final int indSC = Utils.indexOfNotEscaped(myPrintname, SUBCAT);
                int ind;
                if ((indSC > -1) && (indSC < indTT)) {
                        ind = -1;
                } else {
                        ind = indTT;
                }
                String result;
                if (ind > -1) {
                        result = myPrintname.substring(ind + TT_START.length());
                } else {
    	                result = myPrintname;
                }
                ind = Utils.indexOfNotEscaped(result, SUBCAT);
                if (ind > -1) {
	                result = result.substring(0, ind);
                }
                ind = Utils.indexOfNotEscaped(result, PARAM);
                if (ind > -1) {
	                result = result.substring(0, ind);
                }
                return result;                
        }
        
        /**
         * extracts the part of the body of the printname that is the 
         * text entry for the JList
         * @param myPrintname the body of the printname
         * @return the one-line description of this Printname's fun
         */
        public static String extractDisplayText(String myPrintname) {
                String result;
                int ind = Utils.indexOfNotEscaped(myPrintname, TT_START);
                if (ind > -1) {
                        result = myPrintname.substring(0, ind);
                } else {
    	                result = myPrintname;
                }
                ind = Utils.indexOfNotEscaped(result, SUBCAT);
                if (ind > -1) {
	                result = result.substring(0, ind);
                }
                ind = Utils.indexOfNotEscaped(result, PARAM);
                if (ind > -1) {
	                result = result.substring(0, ind);
                }
                
                return result;                
        }
        
        /**
         * Appends the given string insertion to original and 
         * returns the result. If original is already HTML, the appended
         * text will get right before the &lt;/html&gt; tag.
         * If original is no HTML, it will be enclosed in &lt;html&gt;
         * @param original The String that is to come before insertion
         * @param insertion the String to be appended
         * @return the aforementioned result.
         */
        public static String htmlAppend(String original, String insertion) {
                StringBuffer result = new StringBuffer(original);
                int htmlindex = result.indexOf("</html>");
                
                if (htmlindex > -1) {
                        result.insert(htmlindex, insertion);
                } else {
                        result.insert(0,"<html>").append(insertion).append("</html>");
                }
                return result.toString();
                
        }

        /**
         * Prepends the given string insertion to original and 
         * returns the result. If original is already HTML, the appended
         * text will get right after the &lt;html&gt; tag.
         * If original is no HTML, it will be enclosed in &lt;html&gt;
         * @param original The String that is to come after insertion
         * @param insertion the String to be appended
         * @return the aforementioned result.
         */
        public static String htmlPrepend(String original, String insertion) {
                StringBuffer result = new StringBuffer(original);
                int htmlindex = result.indexOf("<html>");
                
                if (htmlindex > -1) {
                        result.insert(htmlindex, insertion);
                } else {
                        result.insert(0,insertion).insert(0,"<html>").append("</html>");
                }
                return result.toString();
                
        }

        /**
         * wraps a single parameter with explanatory text
         * into &lt;dt&gt; and &lt;dd&gt; tags
         * @param which the number of the parameter
         * @return the resulting String, "" if the wanted parameter
         * is not stored (illegal index)
         */
        protected String htmlifyParam(int which) {
                try {
                        String result = "<dt>" + this.paramNames.get(which) + "</dt>"
                        + "<dd>" + this.paramTexts.get(which) + "</dd>";
                        return result;
                } catch (ArrayIndexOutOfBoundsException e) {
                        subcatLogger.warn(e.getLocalizedMessage());
                        return "";
                }
                
        }
        
        /**
         * wraps a single parameter together with its explanatory text into
         * a HTML definition list (&lt;dl&gt; tags).
         * Also the result is wrapped in &lt;html&gt; tags.
         * @param which the number of the parameter
         * @return the resulting definition list, null if the param is not found.
         */
        public String htmlifySingleParam(int which) {
                String text = htmlifyParam(which);
                if (text.equals("")) {
                        return null;
                }
                String result = "<html><dl>" + text + "</dl></html>";
                return result;
        }
        
        /**
         * wraps all parameters together with their explanatory text into
         * a HTML definition list (&lt;dl&gt; tags).
         * No &lt;html&gt; tags are wrapped around here, that is sth. the caller
         * has to do!
         * @return the resulting definition list, "" if which is larger than
         * the amount of stored params
         */
        public String htmlifyParams() {
                if (this.paramNames.size() == 0) {
                        return "";
                }
                StringBuffer result = new StringBuffer("<h4>Parameters:</h4><dl>");
                for (int i = 0; i < this.paramNames.size(); i++) {
                        result.append(htmlifyParam(i));
                }
                result.append("</dl>");
                return result.toString();
        }
        
        /**
         * a testing method that is not called from KeY.
         * Probably things like this should be automated via JUnit ...
         * @param args not used
         */
        public static void main(String[] args) {
                String SandS = "boolean 'and' for sentences$true iff both of the two given sentences is equivalent to true%BOOL#alpha the first of the two and-conjoined sentences#beta the second of the and-conjoined sentences";
                String FandS = "andS";
                Hashtable ht = new Hashtable();
                Printname pn = new Printname(FandS, SandS, ht);
                System.out.println(pn);
                for (int i = 0; i < pn.paramNames.size(); i++) {
                        System.out.println(pn.htmlifySingleParam(i));
                }
                System.out.println(pn.getTooltipText());
                SandS = "boolean 'and' for sentences$true iff both of the two given sentences is equivalent to true%BOOL";
                FandS = "andS";
                pn = new Printname(FandS, SandS, ht);
                System.out.println("*" + pn.getTooltipText());
        }
        
        public String toString() {
                return getDisplayText() + "  \n  " + getTooltipText() + " (" + this.paramNames.size() + ")";
        }

}
