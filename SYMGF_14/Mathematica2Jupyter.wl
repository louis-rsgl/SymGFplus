(* ::Package:: *)
(* :Name: Mathematica2Jupyter *)
(* :Author: https://github.com/divenex *)
(* :Date: 2025-06-04 *)
(* :Summary: Converts Mathematica notebooks (.nb) to Jupyter (.ipynb) or VS Code (.wlnb/.vsnb) format *)
(* :Context: Mathematica2Jupyter` *)
(* :Package Version: 1.1.2 *)
(* :Mathematica Version: 12.0+ *)
(* :Copyright: (c) 2025 divenex (https://github.com/divenex) *)

ClearAll["Mathematica2Jupyter`*", "Mathematica2Jupyter`Private`*"]  (* Clean everything upon reloading *)

BeginPackage["Mathematica2Jupyter`"];

Mathematica2Jupyter::usage = "Mathematica2Jupyter[inputFile, format] 
    converts a Mathematica notebook (.nb) to Jupyter (.ipynb) or VS Code (.wlnb/.wsnb) format.
    format (optional): \"ipynb\" (default) or \"wlnb\"/\"vsnb\".
    Returns the path to the created file upon success, or $Failed if conversion fails.";

Begin["`Private`"];

Mathematica2Jupyter::unparsed = "Unrecognized form encountered during conversion: `1`";

prefix = <|"Title"               -> "# ",
           "Subtitle"            -> "## ",
           "Chapter"             -> "# ", 
           "Section"             -> "---\n## ",
           "Subsection"          -> "### ",
           "Subsubsection"       -> "#### ",
           "Item"                -> "-   ",
           "ItemNumbered"        -> "1.  ",
           "ItemParagraph"       -> "    ",    
           "Subitem"             -> "    -   ", 
           "SubitemNumbered"     -> "    1.  ",
           "SubitemParagraph"    -> "        ",    
           "Subsubitem"          -> "        -   ", 
           "SubsubitemNumbered"  -> "        1.  ",
           "SubsubitemParagraph" -> "            "|>

processItem[TextData[elems_]] := StringJoin[processItem /@ Flatten[{elems}]];  (* Recursive *)

processItem[StyleBox[txt_String, "Input", ___]] := " `" <> StringTrim[txt] <> "` "

processItem[StyleBox[txt_String, FontSlant->"Italic", ___]] := " *" <> StringTrim[txt] <> "* "
    
processItem[StyleBox[txt_String, FontWeight->"Bold", ___]] := " **" <> StringTrim[txt] <> "** "

processItem[fmt_StyleBox] := ExportString[fmt, "HTMLFragment"]

processItem[ButtonBox[txt_String, ___, ButtonData->{___, URL[url_String], ___}, ___]] := 
    " [" <> txt <> "](" <> url <> ") "

processItem[item_?(!FreeQ[#, _GraphicsBox]&)] := ExportString[Rasterize[item], "HTMLFragment"]

cond = (StringContainsQ[#, "$"] && StringFreeQ[#, {"{", "}"}])&

(* Also includes a fix for ExportString bugs producing TeX like \(\text{\textit{2$\sigma$r}}\) or \(x{}^2\) *)
processItem[Cell[box_BoxData, ___] | box_BoxData] := 
    StringReplace[ExportString[box, "TeXFragment"], 
        { "\\text{\\textit{" ~~ str__ ~~ "}}" /; cond[str] :> StringDelete[str, "$"],
         ("\\text{" | "\\textit{") ~~ str__ ~~ "}" /; cond[str] :> StringDelete[str, "$"],
          "\\(" -> " $", "\\)" -> "$ ", "{}" | "\r\n" -> ""}]

processItem[str_String] := str

(* FIX #1: Ignore StyleData cells (used in stylesheets) to prevent errors *)
processItem[_StyleData] := "**[Style Definition - Skipped]**"

processItem[unknown_] := (Message[Mathematica2Jupyter::unparsed, unknown]; "---UNPARSED---")

processText[cnt_, type_] := Lookup[prefix, type, ""] <> StringReplace[processItem[cnt], "\n" -> "\n\n"]

processInput[_?(!FreeQ[#, _GraphicsBox]&)] := "---IMAGE---"

(* FIX #2: Robust version of processInput that handles syntax errors *)
processInput[cnt_] := Module[{expr},
    expr = Quiet[Check[ToExpression[cnt, StandardForm, HoldComplete], $Failed]];
    If[expr === $Failed,
        (* If parsing fails, extract raw text using "Text" format *)
        StringTrim[ExportString[Cell[cnt, "Input"], "Text"]],
        
        (* If parsing succeeds, convert valid code structure *)
        StringReplace[StringTake[
            ToString[expr, InputForm], 
            {14, -2}], ", Null, " | (", Null" ~~ EndOfString) -> "\n"]
    ]
]

typeKey[fmt_] := If[fmt === "ipynb", "cell_type", "languageId"]
contentKey[fmt_] := If[fmt === "ipynb", "source", "value"]
codeValue[fmt_] := If[fmt === "ipynb", "code", "wolfram"]

processCell[style_, Cell[cnt_, ___], fmt_] :=
    AssociationThread[{"kind", "metadata", typeKey[fmt], contentKey[fmt]} -> Switch[style,
        "DisplayFormula" | "DisplayFormulaNumbered", 
                          {1, <||>, "markdown",     StringReplace[processItem[cnt], "$" -> "$$"]},
        "Input" | "Code", {2, <||>, codeValue[fmt], processInput[cnt]},
        _,                {1, <||>, "markdown",     processText[cnt, style]}]]

mergeMarkdownCells[cells_, fmt_] := 
    SequenceReplace[cells, {c__?(#[typeKey[fmt]] === "markdown"&)} :> 
        <|c, contentKey[fmt] -> StringRiffle[Lookup[{c}, contentKey[fmt]], "\n\n"]|>]
                                                                          
Mathematica2Jupyter[inputFile_?FileExistsQ, fmt_String:"ipynb"] := 
    Export[FileBaseName[inputFile] <> "." <> fmt,        
        {"cells" -> mergeMarkdownCells[NotebookImport[inputFile, 
            Except["Output" | "Message"] -> (processCell[#1,#2, fmt]&)], fmt],          
        "metadata" -> {"language_info" -> {"name" -> "wolfram", "codemirror_mode" -> "mathematica", 
            "pygments_lexer" -> "wolfram", "mimetype" -> "application/vnd.wolfram.mathematica"}}}, "JSON"]

End[]

EndPackage[]