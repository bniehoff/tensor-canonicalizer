(*************************************************************************
 * canonicalization.m
 *
 * Copyright 2017 Ben Niehoff
 * ben.niehoff@gmail.com
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *************************************************************************)

(* Mathematica Package *)
(* Created by Mathematica Plugin for IntelliJ IDEA *)

(* :Title: canonicalization *)
(* :Context: canonicalization` *)
(* :Author: ben *)
(* :Date: 2017-01-11 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: 11.0.0.0 *)
(* :Copyright: (c) 2017 Ben Niehoff *)
(* :Keywords: *)
(* :Discussion: *)

BeginPackage["canonicalization`"]
(* Exported symbols added here with SymbolName::usage *)

(* Sorry, have not bothered to define any usage messages *)


(**** Set up C compilation ****)


Needs["CompiledFunctionTools`"];

(* You need to configure this to point to your own installed C compiler! *)
Needs["CCompilerDriver`"];
$CCompiler = {
  "Compiler" -> CCompilerDriver`GenericCCompiler`GenericCCompiler,
  "CompilerInstallation" -> "C:\\Strawberry\\c\\bin\\gcc.exe"}

(**** COMPILE HELPER FUNCTIONS ****)

(* First define some compilation helper functions *)

(* Macro is designed to access the source code of a Function body and return it wrapped in Hold, with the
appropriate variables plugged in *)
Clear[Macro];
SetAttributes[Macro,HoldAll];
(* One trivial definition so that the blue highlighting goes away *)
Identity[Macro[any___]]^:=Macro[any];

(* We create a specialized version of Hold for dealing with Macros, so that we don't erroneously release other
Holds that the programmer might have actually intended to stay! *)
SetAttributes[HoldMacro,HoldAll];
(* One trivial definition so that the blue highlighting goes away *)
Identity[HoldMacro[any___]]^:=HoldMacro[any];

(* Various specialized Hold functions for destructuring a function call and reassembling it, without prematurely
evaluating its arguments (just in case an argument is a global variable that has been localized!) *)
SetAttributes[HoldArg,HoldAll];
Identity[HoldArg[any___]]^:=HoldArg[any];


(* We leave Macro inert and instead define a function that accesses the contents. Notice that the Macro head
already has the HoldAll attribute; thus getMacroSource does not need HoldAll. In fact, we *want* it to evaluate! *)
getMacroSource[Macro[fun_[args___]]]:=
    With[{def=OwnValues[fun][[1,2]],heldargs=ReleaseHold@(HoldArg/@Hold[args])},
      If[Head[def]===Function,
        Replace[MapAt[HoldMacro,def,{2}][heldargs],HoldArg[arg_]:>arg,Infinity]
      ]];

(* Default case *)
getMacroSource[expr:Except[_Macro]]:=expr;

(* Replace any macros in a block of code with their source code, wrapped in HoldMacro *)
SetAttributes[injectMacros,HoldAll];
injectMacros[expr_]:=
(* search for macros in reverse order of depth *)
    With[{positions=Reverse@SortBy[Position[expr,HoldPattern@Macro[_]],Length]},
      If[Length[positions]>0,
      (* Traverse the list of macro positions *)
        Fold[
          With[{source=getMacroSource@Extract[#1,#2]},
          (* Recurse through the macro source to look for more macros *)
          (* Always inserts the deepest nested macros first! *)
            ReplacePart[#1,injectMacros[source],#2]]&,
          expr,
          positions],
      (* else *)
      (* Make sure there is an exit from recursion *)
        expr]
    ]


(* Meta can be used with any expression, but especially as Meta@Compile[...]. Meta keeps its argument wrapped
in Hold, looks for any unexpanded Macro heads, and expands them *)
Clear[Meta]
SetAttributes[Meta,HoldFirst];
Options[Meta]={Debug->False};

(* Expand Macro heads to source code wrapped in Hold with appropriate values plugged in; then remove the inner
Hold heads to inject the source code.  Finally remove the outer Hold *)
(* Note that Debug is a (deprecated) Mathematica function already and we are abusing it!  But we do not make
  any definitions to it; only the replacement rules you see here.  Take a look at the functions below in this
  file for how it's meant to be used.  The most common useage is Debug@Print["Some useful statement"] *)
Meta[expr_,OptionsPattern[Meta]]:=
    With[{debugrule=
        If[OptionValue[Debug]===True,
          HoldPattern[Debug[any___]]:>any,
          HoldPattern[Debug[any___]]:>Null]},
      ReleaseHold@
          Replace[
            injectMacros[Hold[expr]],
            {HoldMacro[any___]:>any,debugrule},
            Infinity]
    ];



(**** UTILITIES FOR BUILDING DATA STRUCTURES ****)

(* Transforms group generators into lists *)
listifyGenerators[PermutationGroup[{}],_]:={};
listifyGenerators[group_,length_]:=(PermutationList[#,length]&/@GroupGenerators[group]);



(* Macro to build a depth-limited cube Schreier tree from a non-degenerate set of generators R *)
(* We assume that the tree has already been pre-allocated and may have some valid nodes in it *)
(* R must already include any of the distinct inverses that need to be considered! *)
(* Instead of Rgens, we should use the full packed data structure, but it is only partially built! *)
buildDepthLimitedTree=Function[{data,root,depth,length,numgens},
  Module[{tree,visited,levelend,levelstart,visitedcount,currentdepth,i,j,new},
  (* Initialize tree *)
    tree=Array[0&,{2,length}];
    tree[[1,root]]=-1;

    (* Initialize the array of visited elements *)
    visited=Array[0&,length];
    visited[[1]]=root;
    levelstart=levelend=visitedcount=1;

    (* Build up tree one level at a time *)
    currentdepth=1;
    Catch[
      While[currentdepth<=depth&&levelstart<=levelend&&visitedcount<length,
      (* Iterate over everything in the current level *)
        For[i=levelstart,i<=levelend,i++,
        (* Try all the generators on items in the current level *)
          For[j=2,j<=numgens+1,j++,(* Offset because Rgens start on second row of data! *)
          (* Check if we find anything new *)
            new=data[[j,visited[[i]]]];
            If[tree[[1,new]]==0,(* We have found a new element! *)
              tree[[1,new]]=visited[[i]]; (* Set the new tree element *)
              tree[[2,new]]=j;(* Record the group generator that got us here *)
              visitedcount++;(* Increment next level end pointer *)
              visited[[visitedcount]]=new;(* Add new element to visited *)
            ];

            (* Check if we are done early *)
            If[visitedcount==length,Throw[Null]];
          ];
        ]; (* End outer For *)

        (* Now we have done everything we can at this level *)
        levelstart=levelend+1;
        levelend=visitedcount;
        currentdepth++;
      ]]; (* end Catch *)

    (* Return the completed tree (CopyTensor will be called) *)
    tree
  ]];



(* Given a symmetry data structure and a tree, function returns group element which takes root to point,
or {0,0,...} if point is not in tree *)
(* We must take the tree separately, because the data structure is always partially built when this runs *)
cosetRep=Function[{data,tree,point,length},
  Module[{h,p},
    h=Range[length];(* Initialize h to identity *)
    p=point;

    If[tree[[1,point]]==0,
      h=Array[0&,length],(* point not in tree, return zero; otherwise continue *)
      While[tree[[1,p]]!=-1,
        h=h[[data[[tree[[2,p]]]]]];(* Compose h with generator *)
        (* Note the order, since the group action is [[]], we must nest the new generator inside in order to
         obtain the path from root to leaf *)
        p=tree[[1,p]]
      ]];

    (* Return h *)
    h]];



(* This takes a lexicographically-ordered SGS and computes the special data structure we need *)
buildCubeSchreierVector = Meta[
  Compile[{{Sgens,_Integer,2}},
    Module[{data,numgens,length,id,zero,stabilizers,pos,gen,h,g,y,invhg,maxrows,dataincrement,trees,treepointer,
        rgenrow,sgencount,i,foundq,depth},
      (* Get dimensions *)
      {numgens,length}=Dimensions[Sgens];

      Debug@Print["We have ",numgens," generators of length ",length,", given by\n",MatrixForm[Sgens]];

      (* Some array constants *)
      id = Range[length];
      zero = Array[0&,length];

      (* Since we assume Sgens are SORTED, then each stabilizer group G(i) is just a prefix of Sgens.
        We can store this information in an array stabilizers.  Then for 1 <= i <= length, stabilizers[[i]]
        contains the number of rows of Sgens which are to be included as generators of G(i).  That number may be
        zero, if the stabilizer group G(i) is trivial.  Now, let's populate stabilizers, from G(1) to G(n) *)
      stabilizers = zero;
      pos = 1;
      stabilizers[[pos]] = numgens;
      For[gen=numgens,gen>=1,gen--,
        While[pos<length && Sgens[[gen,pos]]==pos,
          pos++;
          stabilizers[[pos]] = gen;
        ];
      ];

      Debug@Print["Stabilizer groups indexed into generator set:\n",MatrixForm@{id, stabilizers}];

      (* Now we have the ability to easily walk backward over the stabilizer groups *)

      (* Initialize data object *)
      maxrows = 1 + numgens;
      data = dataincrement = Array[0&,{maxrows,length}];

      (* Initialize trees to worst case size *)
      (* Note:  treepointer is always an odd number *)
      trees = Array[0&,{2*length,length}];
      treepointer = 1;

      (* Initialize Rgens *)
      (* Rgens start on 2nd row of data *)
      rgenrow = 2;

      (* Initialize group elements so compilar knows they are arrays *)
      h = g = invhg = id;

      (* Now implement the algorithm in Cooperman & Finkelstein *)
      depth = 0;
      sgencount = 0;
      For[pos = length, pos >= 1, pos--,
        (* Walk down from the end until we get to a new stabilizer group *)
        If[stabilizers[[pos]] == sgencount, Continue[]];

        (* Now we have a new stabilizer group.  Update sgentcount *)
        sgencount = stabilizers[[pos]];

        Debug@Print["Stablizer group found at position ",pos," using the first ",sgencount," entries of Sgens"];

        (* Initialize tree *)
        trees[[treepointer;;treepointer+1]] = {zero,zero};
        trees[[treepointer,pos]] = -1;

        Debug@Print["New tree started at tree pointer ",treepointer];
        Debug@Print["Trees are now\n",MatrixForm[trees[[1;;treepointer+1]]]];

        (* Next we want to find a g in the generating set such that g[[y]] is not in the tree, for some y in the tree *)
        y = pos;
        foundq = False;
        Catch[
          While[y <= length,
            For[i = 1, i <= sgencount, i++,
              If[(trees[[treepointer,y]] != 0) && (trees[[treepointer,Sgens[[i,y]]]] == 0),
                g = Sgens[[i]];
                Debug@Print["New orbit point found at ",g[[y]],", mapped from ",y];
                foundq = True;
                Throw[Null];
              ];
            ];
            y++;
          ];
        ];

        (* If the tree is non-trivial, add the tree pointer to the first row of data *)
        If[foundq,data[[1,pos]]=treepointer];

        (* Now process tree for more orbit points *)
        While[foundq,
          (* We have found a new orbit point; we need to amend the tree *)
          (* Get group element that maps root to leaf *)
          h = Macro@cosetRep[data,trees[[treepointer;;treepointer+1]],y,length];
          
          Debug@Print["Group element which maps ",y," to ",pos," is ",h];

          (* Pre-expand allocation (linearly) if needed *)
          If[rgenrow > maxrows-1, (* offset due to initial row of tree pointers *)
            data=Join[data,dataincrement];
            maxrows+=numgens+1];

          (* Append hg to Rgens (need to reverse order because [[]] is group action) *)
          data[[rgenrow]]=g[[h]];
          rgenrow++;
          depth += 2;

          (* If inverse is distinct, also append inverse *)
          invhg[[g[[h]]]]=id;
          If[invhg!=g[[h]],
            data[[rgenrow]]=invhg;
            rgenrow++];

          Debug@Print["Rebuilding tree with ",rgenrow-2," Rgens to depth ",depth];

          (* Build cube tree based on Rgens *)
          trees[[treepointer;;treepointer+1]] = Macro@buildDepthLimitedTree[data,pos,depth,length,rgenrow-2];

          Debug@Print["Tree ",treepointer," rebuilt.  Trees are now\n",MatrixForm[trees[[1;;treepointer+1]]]];

          (* Find next y and g, if they exist *)
          y = pos;
          foundq = False;
          Catch[
            While[y <= length,
              For[i=1,i <= sgencount,i++,
                Debug@Print["Checking tree:  y = ",y," maps to g[[y]] = ",Sgens[[i,y]]];
                If[(trees[[treepointer,y]] != 0) && (trees[[treepointer,Sgens[[i,y]]]] == 0),
                  g = Sgens[[i]];
                  Debug@Print["New orbit point found at ",g[[y]]];
                  foundq = True;
                  Throw[Null];
                ];
              ];
              y++;
            ];
          ];

          (* Repeat While loop until tree is complete *)
        ]; (* End While single tree loop *)

        (* If we have built a tree, increase tree pointer *)
        If[data[[1,pos]] != 0, treepointer += 2];

        (* Proceed to next position *)
      ]; (* End For main loop *)

      (* Now we have a data object with Rgens, and tree pointers into a separate tree object *)

      (* Need to properly offset the tree pointers *)
      For[i=1,i<=length,i++,
        If[data[[1,i]] != 0, data[[1,i]] += rgenrow-1]];

      (* Return the data object with tree object attached *)
      Join[Take[data,rgenrow-1],Take[trees,treepointer-1]]
    ] ,
    CompilationTarget->"C",RuntimeOptions->"Speed"
  ], (* End Compile *)
  Debug->False
]; (* End Meta *)




(**** MACROS FOR BUILDING MAIN ALGORITHM ****)



(*** signedSift ***)

(* Checks whether perm is a member of the stabilizer group G(i) in slotdata, up to sign.
Returns the sign (1 or -1) if so; otherwise returns 0 *)
signedSift=Meta[
  Function[{slotdata,i,perm,length},
    Module[{j,g,h,invh,id,sign,t},
      (* Initialize variables *)
      t=0;
      g=perm;
      h=invh=id=Range[length];

      Debug@Print["Slot configuration: ",g];

      (* Attempt to bring perm back to the identity using cosetRep for each of its entries in turn *)
      sign=0;
      For[j=i,j<=length-2,j++,
        (* Get the tree pointer *)
        t=slotdata[[1,j]];

        Debug@Print["Matching position ",j];

        If[t==0,
          (* Stabilizer group is trivial, we had better have the correct slot at this position *)
          Debug@Print["Trivial tree"];
          If[g[[j]]!=j,
            Debug@Print["Match failed"];
            Break[]],
          (* else *)

          (* Otherwise, get cosetRep and modify g *)
          h=Macro@cosetRep[slotdata,slotdata[[t;;t+1]],g[[j]],length];

          (* Check if point is in tree *)
          If[h[[1]]==0,
            Debug@Print["Point not in tree.  Match failed."];
            Break[]];

          Debug@Print["Permutation that maps ",j," to ",g[[j]]," is ",h];

          (* Otherwise, modify g *)

          (* First, invert h *)
          invh[[h]]=id;

          (* Now get new g *)
          g=invh[[g]];

          Debug@Print["New permutation to be tested: ",g];

        ];
      ];

      (* Check to see if we succeeded *)
      If[j==length-1,
        sign=g[[length]]-g[[length-1]]];

      (* Return sign *)
      sign
    ]
  ],
  Debug->False
];



(*** symmetricSubgroups ***)

(* Finds all (anti)symmetric subgroups in slotdata.  Returns an array with each slot marked *)
symmetricSubgroups=Meta[
  Compile[{{slotdata,_Integer,2}},
    Module[{subgroups,length,i,j,k,g,id,sign,symnumber},
      (* Get length *)
      length=Length[slotdata[[1]]];

      (* Initialize subgroups *)
      subgroups=Array[0&,length];

      (* Initialize group element *)
      g=id=Range[length];

      (* Force iterators to be integers *)
      i=j=k=sign=1;

      (* Step through slots and find symmetric pairs *)
      symnumber=0;
      For[i=1,i<=length,i++,
        If[subgroups[[i]]!=0,Continue[]];

        (* Search for symmetric pairs *)
        j=i;
        k=i+1;
        While[k<=length-2,
          g=id;
          g[[{j,k}]]=g[[{k,j}]];

          sign=Macro@signedSift[slotdata,j,g,length];

          If[sign!=0,
            If[j==i,
              symnumber++;
              subgroups[[j]]=sign*symnumber];
            subgroups[[k]]=subgroups[[j]];
            j=k];
          k++];
      ];

      (* Return subgroups *)
      subgroups
    ], (* End Module *)
    CompilationTarget->"C",RuntimeOptions->"Speed"
  ],(* End Compile *)
  Debug->False
]; (* End Meta *)


(*** zeroConfigurationQ ***)

(* takes a sorted list of index configurations, and compares adjacent ones to see if we get zero *)
zeroConfigurationQ=Function[{configurations,number,length},
  Module[{i,j,output},
    i=1;
    j=1;
    output=False;
    For[i=1,i<=number-1,i++,
      j=1;
      While[j<=length-2&&(configurations[[i,1,j]]==configurations[[i+1,1,j]]),j++];
      If[j==length-1&&(configurations[[i,1,length-1]]==configurations[[i+1,1,length]]),
        output=True;
        Break[]]];
    output
  ]];


(*** removeDuplicates ***)

(* takes a sorted list of index configurations, and removes adjacent duplicates *)
removeDuplicates=Function[{configurations,number,length},
  Module[{i,j,k,output},
    i=1;
    j=1;
    k=1;
    output=configurations;
    For[i=2,i<=number,i++,
      j=1;
      While[j<=length&&(configurations[[i,1,j]]==configurations[[i-1,1,j]]),j++];
      If[j!=length+1,
        k++;
        output[[k,1]]=configurations[[i,1]];
      ];
    ];
    output[[1;;k]]
  ]];



(**** MAIN FUNCTION ****)


(* This calculates the canonical representative under the double coset SgD.  It uses a version of the algorithm
specialized to the types of dummy symmetries one can actually encounter, and thus is not usable for generic
double cosets. *)
improvedButlerPortugal = Meta[
  Compile[{{initialconfig,_Integer,1},{slotdata,_Integer,2},{subgroups,_Integer,1},{labeldata,_Integer,2}},
    Module[{values,groups,finalconfig,symmetries,length,slot,label,value,pair,i,j,k,orbit,orbitcount,labelshift,
      tree,least,leastslot,leastend,leasts,leastcount,leastsarraysize,leastsarrayincrement,sign,id,d,s,g,invg,invs,
      invgs,sinvg,zero,zeroq,configs,configcount,nextconfigs,nextconfigcount,nextarraysize,nextarrayincrement,symtest,
      symnumber,advancesymnumberq,labelpartner,visitedlabel,visitedlabelpartner,leastpartner,leastset,leastsetcount,confignumber,
      thissym,thissympartner,labelsym,shiftedsyms,visitedsyms,sympoint,orbitlabel,symnumbers,visitedglobalsyms,position},

      (* Initializing all variables *)

      (* position of least label in group *)
      values=labeldata[[1]];
      length=Length[values];

      (* 0, 1, 2, or -2 to indicate how corresponding label can be exchanged *)
      (* Can also have codes 3, 4 to indicate dummy indices with no metric *)
      groups=labeldata[[2]];

      (* Set up some default arrays *)
      id=Range[length];
      zero=Array[0&,length];

      (* Initialize symmetries array *)
      symmetries=shiftedsyms=visitedsyms=symnumbers=visitedglobalsyms=zero;
      thissym=thissympartner=labelsym=0;

      (* Initialize group elements *)
      d=g=invg=s=invs=invgs=sinvg=id;

      (* Initialize configuration array with the initial configuration *)
      configs={{initialconfig,id}};
      configcount=1;

      (* Initialize nextconfigs array *)
      nextconfigs=nextarrayincrement=Array[{zero,zero}&,length];
      nextarraysize=length;
      nextconfigcount=0;

      (* Initialize slot counter *)
      slot=1;

      (* Force some variables to be integer types *)
      pair=label=sign=orbitlabel=sympoint=position=labelshift=i=j=k=1;
      leastslot=leastend=least=value=length;
      confignumber=0;

      (* Initialize orbit array and leasts *)
      orbit =Array[0&,length];
      leasts=leastsarrayincrement=Array[0&,{length,3}];
      leastset=Array[0&,{length,2}];
      leastsarraysize=length;
      orbitcount=leastcount=leastsetcount=0;

      Debug@Print["Initial configuration: ",initialconfig];

      (*********************************************)
      (***** Begin main loop ***********************)
      (*********************************************)

      (* Step through slots one at a time, and find which labels can be mapped into their orbits *)
      zeroq=False;
      symnumber=-1;
      (* visitedglobalsyms will track when a given slot's symmetry has been visited *)
      visitedglobalsyms=zero;
      Catch[
        For[slot=1,slot<=length-2,slot++,
          Debug@Print["Begin slot ",slot];

          (*********************************************)
          (***** Find the orbits ***********************)
          (*********************************************)

          (* Get tree pointer *)
          tree=slotdata[[1,slot]];

          (* Initialize orbit *)
          orbit[[1]]=slot;
          orbitcount=1;

          (* Get full orbit *)
          If[tree!=0,
          (* Non-trivial tree; scan to the right to get orbit *)
            For[i=slot+1,i<=length-2,i++,
              If[slotdata[[tree,i]]!=0,
                orbitcount++;
                orbit[[orbitcount]]=i];
            ];
          ];

          Debug@Print["Orbit of slot ",slot," is ",orbit[[1;;orbitcount]]];

          (*********************************************)
          (***** Get the least values in orbit *********)
          (*********************************************)

          Debug@Print["Analyzing orbit..."];

          (* Obviously there was some confusion in the comments below about getting things to work;
            I will leave this here *)

          (* Find the least available index in any of the slots, subject to any of the configurations *)
          (* For each least element, record its slot(s) in leasts *)
          (* Note:  If any elements in the orbit have entries in symmetries array, we must scan
            (to the right in the config) for all elements with that symmetry number; the orbit is enlarged! *)
          (* Note 2:  In order to correctly process propagated symmetries, we need to distinguish between
            orbit points which can be reached via the slot group, and those which can be reached via the
            propagated symmetries.  Therefore we require two passes:  First to enter everything that comes
            directly from the slots group, and second to fill in the gaps from propagated symmetries *)
          (* Note 3:  No, we want to do this in a single pass, so that everything enters in order *)

          (* We need to re-think this section.  Remember that entries in the symmetries/shiftedsyms array are
            SLOT-ATTACHED LABEL SYMMETRIES, so they should be treated the same as label symmetries for every
            fixed slot arrangement (i.e. every configuration).  So, the scan through the array needs to happen
            at the time that we determine an orbit point's VALUE; i.e., at the beginning of the loop.  The
            visitedsyms array concept might not actually make sense...what we REALLY need to know, to avoid
            redundant counting, is whether a symmetry from subgroups has been used...subgroups contains actual
            slot symmetries.  The criterion to ignore a possible nextconfig entry is precisely: label symmetry is
            equivalent to slot symmetry.  The only purpose of symmetries/shiftedsyms is to keep track of slot
            symmetries which have been promoted to label symmetries.  Perhaps we could get away with scanning
            only EVEN numbered symmetries/shiftedsyms, because the odd-numbered ones are guaranteed to match
            against slot symmetries. *)
          least=length;
          leastcount=0;
          For[i=1,i<=configcount,i++,

            Debug@Print["Config ",i];

            (* Get the shifted symmetry set in order to iterate over unused symmetry equivalents *)
            shiftedsyms=symmetries[[configs[[i,2]]]];

            Debug@Print["Shifted symmetries: ",shiftedsyms];

            (* Iterate through the orbit *)
            (*visitedsyms=zero;*)
            For[j=1,j<=orbitcount,j++,

              (*Debug@Print["Orbit point ",orbit[[j]]];*)

              (* Get value at gi[[orbit[[j]]]]]] *)
              value=values[[configs[[i,1,orbit[[j]]]]]];
              sympoint=orbit[[j]];

              Debug@Print["Value at orbit point ",orbit[[j]]," is ",value];

              (* However, the value we obtain here might not be the least possible value at this point, if it
                has an entry in shiftedsyms *)
              (* We also need to check whether there is a smaller value that can be put at this slot via symmetries *)
              If[(shiftedsyms[[orbit[[j]]]]!=0) && (EvenQ[shiftedsyms[[orbit[[j]]]]]),
                (* This point has extra symmetries which were propagated along dummy contraction *)
                Debug@Print["This orbit point has a propagated symmetry ",shiftedsyms[[orbit[[j]]]]];
                Debug@Print["Scanning shiftedsyms to the right from slot ",slot," to search for lower value"];

                For[k=slot,k<=length,k++,
                  If[(shiftedsyms[[k]]==shiftedsyms[[orbit[[j]]]]) && (k!=orbit[[j]]) && (values[[configs[[i,1,k]]]]<value),
                    value=values[[configs[[i,1,k]]]];
                    sympoint=k;
                  ];
                ];

                Debug@Print["Final value at orbit point ",orbit[[j]]," is ",value];
              ];

              (* Check if we need to reset the least counter *)
              If[value<least,
                least=value;
                Debug@Print["New least value ",least," found"];
                (*leastslot=orbit[[j]]];*)
                leastcount=0];

              (* Check if we need to add something to the leasts array *)
              If[value==least,
                leastcount++;

                (* Check to see if we need to grow the array *)
                If[leastcount>leastsarraysize,
                  leasts=Join[leasts,leastsarrayincrement];
                  leastsarraysize+=length];

                (* Add the new item *)
                leasts[[leastcount]]={i,sympoint,orbit[[j]]};
                Debug@Print["Orbit point ",orbit[[j]]," added to leasts array"];
                Debug@Print["leasts array is now\n", MatrixForm@Transpose[leasts[[1;;leastcount]]]];
              ];
            ]; (* End For j *)
          ]; (* End For i *)

          (* Sort leasts by configuration number, so that we can tell when we are still talking about
          the same configuration as the previous one *)
          (* Actually, this shouldn't be necessary; they are already grouped by configuration number
          because of the structure of the above loop *)
          (*leasts[[1;;leastcount]]]=Sort[leasts[[1;;leastcount]]]];*)

          Debug@Print["values:  ",values];

          Debug@Print["Least value in orbit is ",least];

          Debug@Print["Least value is found in following configurations and slots:\n",
            MatrixForm@Transpose[leasts[[1;;leastcount]]]];

          (*********************************************)
          (***** Iterate over the leasts ***************)
          (*********************************************)

          (* Iterate through all of the leasts, grouped into leastsets which are the set of leasts which all
          came from the same configuration *)
          (* For each configuration and each slot in orbit, if we can map to the least value, then make
          appropriate label swaps and add new configuration to nextconfigs *)
          nextconfigcount=0;
          i=1;
          While[i<=leastcount,
          (* Get the next leastset, increase i accordingly *)
            confignumber=leasts[[i,1]];
            leastsetcount=0;
            While[(i<=leastcount)&&(leasts[[i,1]]==confignumber),
              leastsetcount++;
              leastset[[leastsetcount]]=leasts[[i,2;;3]];
              i++];
            (* No further increment of i needed in the outer While! *)

            Debug@Print["Leastset of ",leastsetcount," elements for configuration ",
              confignumber," accumulated up to i = ",i];

            (* We will need the configuration and its inverse several times *)
            {g,s}=configs[[confignumber]];
            invg[[g]]=id;
            (*invs[[s]]=id;
            invgs[[g[[s]]]]=id;*)
            sinvg = s[[invg]];

            (* symmetries array needs to be accessed with invgs *)

            (* Within each leastset, we must make two passes:  First to find any potential new symmetries to add,
            and second to add entries to nextconfigs for each unique symmetry.  This must be done in two passes
            in order to catch the dummy partners of the newly-found symmetry *)

            (*********************************************)
            (*** First pass: find & extend symmetries ****)
            (*********************************************)

            (* Iterate through the leastset to look for symmetries *)
            (* This should no longer require sifting! *)
            Debug@Print["First pass through leastset to find and propagate symmetries"];
            Debug@Print["Symmetries array is ",symmetries];
            thissym=thissympartner=0;
            (* In visitedsyms, put the label that we encounter in the first occurence of a symmetry *)
            visitedsyms=zero;
            symnumbers=zero;
            For[j=1,j<=leastsetcount,j++,
            (* Get label at (d.g.s)[[orbit[[j]]]] *)
              label=g[[leastset[[j,1]]]];

              Debug@Print["First pass: Processing least element with label ",label," found in configuration ",
                confignumber," at slot ",leastset[[j,1]]," originating from orbit point ",leastset[[j,2]]];

              (* Symmetry checks happen only if our label belongs to a non-trivial label group *)
              If[(groups[[label]]!=0)&&(subgroups[[invg[[label]]]]!=0),

                Debug@Print["Non-trivial subgroups entry found: ",subgroups[[invg[[label]]]]];

                (* Use a few conditions to skip any labels whose symmetries are already entered *)
                Debug@Print["Checking symmetries array at position ",sinvg[[label]]];

                (* symmetries[[sinvg[[label]]]] gives the (per-valuegroup) symmetry group that has already been
                entered.  So we MUST proceed if symmetries[[sinvg[[label]]]] == 0.  However, if
                symmetries[[sinvg[[label]]]] != 0, then whether we proceed depends on the following:

                1.  Is symmetries[[sinvg[[label]]]] odd?  Then do not proceed (Continue[])

                2.  Is symmetries[[sinvg[[label]]]] even?  Then it depends whether it came from propagating dummies
                  from a symmetry on THIS leastset.  So we need a way to record the symmetries encountered within
                  a given leastset

                2a.  If symmetries[[sinvg[[label]]]] is even and from a *previous* leastset, we do not want to overwrite
                  it, so Continue[]

                2b.  If symmetries[[sinvg[[label]]]] is even and from THIS leastset, then we want to overwrite it ONLY
                  when the symmetry group is the original (odd-numbered) one that gave us this one by dummy
                  propagation.  Otherwise Continue[] *)

                (* Addendum:  This is not the whole story.  Even if symmetries[[sinvg[[label]]]]==0, we only want to
                proceed if visitedglobalsyms[[invg[[label]]]] is also zero *)

                (* Now let's try to implement the above conditions *)
                Which[
                  symmetries[[sinvg[[label]]]] == 0,
                    If[visitedglobalsyms[[sinvg[[label]]]]==0,
                      Debug@Print["Subgroup ", subgroups[[invg[[label]]]], " gives a new symmetry; processing"];
                      Null,
                      Debug@Print["*Apparent* new subgroup found, but this slot has been seen before; skipping to next element"];
                      Continue[]
                    ],
                  OddQ@symmetries[[sinvg[[label]]]],
                    Debug@Print["Symmetry ", symmetries[[sinvg[[label]]]], " already entered; skipping to next element"];
                    Continue[],
                  (* If we reach here, then symmetries[[invg[[label]]]] is even *)
                  (* Check if the current (even) symmetry came from a previous leastset *)
                  visitedsyms[[Abs@symmetries[[sinvg[[label]]]]-1]] == 0,
                    Debug@Print["Symmetry ", symmetries[[sinvg[[label]]]],
                      " entered via dummy propagation in prior leastset; skipping to next element"];
                    Continue[],
                  (* Check if the current (even) symmetry is from THIS leastset and
                    the symmetry group is the original one *)
                  Abs@symmetries[[sinvg[[label]]]] - 1 == Abs@symnumbers[[Abs[subgroups[[invg[[label]]]]]]],
                    Debug@Print["Symmetry ", symmetries[[sinvg[[label]]]],
                      " came from dummy propagation of symmetry ", symnumbers[[Abs[subgroups[[invg[[label]]]]]]],
                      " found in THIS leastset; processing to allow overwrite"];
                    advancesymnumberq=True;
                    Null,
                  True,
                    Debug@Print["Symmetry ", symmetries[[sinvg[[label]]]],
                      " came from dummy propagation in this leastset, but not from subgroup ",
                      subgroups[[invg[[label]]]], "; do not allow overwrite"];
                    Continue[];
                ];


                (* Determine whether to increase the global symnumber *)
                If[(symnumbers[[Abs[subgroups[[invg[[label]]]]]]]==0),
                  If[symmetries[[sinvg[[label]]]]==0,
                  (* Advance global symnumber to next odd number *)
                    (symnumber+=2;
                    (* Record the symnumber of this subgroup within this leastset *)
                    symnumbers[[Abs[subgroups[[invg[[label]]]]]]]=symnumber;
                    Debug@Print["Global symnumber advanced to ",symnumber]),
                  (* If we are re-evaluating a partner label, re-use original symnumber *)
                    (symnumbers[[Abs[subgroups[[invg[[label]]]]]]]=
                        Sign[symmetries[[sinvg[[label]]]]]*(Abs[symmetries[[sinvg[[label]]]]]-1))
                  ];
                ];

                Debug@Print["Symnumbers array is ",symnumbers];


                (* Set the names for the current symmetries being evaluated *)
                thissym=Sign[subgroups[[invg[[label]]]]]*symnumbers[[Abs[subgroups[[invg[[label]]]]]]];
                thissympartner=Sign[subgroups[[invg[[label]]]]]*(symnumbers[[Abs[subgroups[[invg[[label]]]]]]]+1);

                Debug@Print["thissym = ",thissym,";  thissympartner = ",thissympartner];

                (* Check whether we have a new symmetry.  We only want to enter data once we have at least a pair *)
                (* Note that visitedsyms uses the odd-number convention *)
                If[visitedsyms[[Abs@thissym]]==0,
                  visitedsyms[[Abs@thissym]]=label;
                  visitedglobalsyms[[sinvg[[label]]]]=1;
                  Debug@Print["One element of subgroup ",subgroups[[invg[[label]]]]," found at label ",label];
                  Continue[]];

                (* Otherwise, we have found a new symmetry that needs to be entered *)
                Debug@Print["(Anti)-Symmetric subgroup found"];

                (* Get label of the first-visited element of this symmetry *)
                visitedlabel=visitedsyms[[Abs@thissym]];
                visitedglobalsyms[[sinvg[[visitedlabel]]]]=1;

                (* If label belongs to group 1 (component indices with same name) and slot exchange is antisymmetric, then we have zero *)
                If[groups[[label]]==1&&thissym<0,
                  Debug@Print["Zero detected!"];
                  zeroq=True;
                  Throw[Null]];

                (* Make entries into symmetries array *)
                symmetries[[sinvg[[label]]]]=thissym;
                symmetries[[sinvg[[visitedlabel]]]]=thissym;

                (* For dummy pairs, propagate to the partner label *)
                If[groups[[label]]==2||groups[[label]]==-2||groups[[label]]==3||groups[[label]]==4,
                  (* In most cases, it is straightforward to find the labelpartner; however, for group 4,
                    we need to shift in the opposite direction *)

                  Debug@Print["Propagating symmetry along dummy pairs"];
                  If[OddQ[visitedlabel-least] || groups[[visitedlabel]]==4,
                    visitedlabelpartner=visitedlabel-1,
                    visitedlabelpartner=visitedlabel+1];
                  If[OddQ[label-least] || groups[[label]]==4,
                    labelpartner=label-1,
                    labelpartner=label+1];
                  visitedglobalsyms[[sinvg[[visitedlabelpartner]]]]=1;

                  Debug@Print["least: ",least,",  label: ",label,",  labelpartner: ",labelpartner,
                    ",  visitedlabel: ",visitedlabel,",  visitedlabelpartner: ",visitedlabelpartner];

                  (* Check whether label is the partner of an already-existing entry *)
                  (* Subsumes the case where label is the same as visitedpartner *)
                  If[symmetries[[sinvg[[labelpartner]]]]==thissym,
                  (* Label is the partner of already-existing entry *)
                  (* Check for zero *)
                    (If[(groups[[label]]==2&&thissym<0)||(groups[[label]]==-2&&thissym>0),
                      Debug@Print["Zero detected!"];
                      zeroq=True;
                      Throw[Null]]),

                  (* Otherwise, propagate to partners as normal *)
                    (If[symmetries[[sinvg[[visitedlabelpartner]]]]!=0,
                      (symmetries[[sinvg[[labelpartner]]]]=thissympartner),
                      (symmetries[[sinvg[[labelpartner]]]]=thissympartner;
                      symmetries[[sinvg[[visitedlabelpartner]]]]=thissympartner)];

                    (* Also, check whether any symmetries on the other side agree in sign *)
                    If[(subgroups[[invg[[labelpartner]]]]==subgroups[[invg[[visitedlabelpartner]]]])&&
                        ((subgroups[[invg[[labelpartner]]]]>0&&thissympartner<0)||
                            (subgroups[[invg[[labelpartner]]]]<0&&thissympartner>0)),
                      Debug@Print["Zero detected!"];
                      zeroq=True;
                      Throw[Null]])
                  ]; (* End if symmetries *)
                ]; (* End If dummy partners *)

                Debug@Print["Symmetry array is now: ",symmetries];
              ]; (* End If symmetry exists *)
            ];(* End For j *)


            (* Get the shifted symmetry set in order to check symmetry equivalents *)
            (*shiftedsyms=symmetries[[configs[[confignumber,2]]]]]];*)

            (*********************************************)
            (* Second pass: add elements to nextconfigs **)
            (*********************************************)

            (* We also need to re-evaluate this section.  The current criteria for when to skip an entry is whether
              it belongs to a symmetry group which has already been visited this iteration.  Instead we want to allow
              some amount of duplication so that zero can be properly detected.  So, the correct logic is:
              Is this label exchange equivalent to a slot exchange?  So we should only remove redundancy within
              a symmetric or antisymmetric pool of SLOT symmetries.  Thus we should refer to the original
              subgroups array, which has all of the slot symmetries marked.

              We still need to track the visitedsyms (from the symmetries array) so that we know whether we have
              seen the first of a group or not.

              Actually, I think we only need to track visited subgroups? (yes) *)

            (* Second pass: select a single element from each symmetry group to add to nextconfigs *)
            Debug@Print["Second pass through leastset to add elements to nextconfigs"];

            (* Note:  Here visitedsyms will refer to visited entries of subgroups, not the symmetries array! *)
            visitedsyms=zero;
            For[j=1,j<=leastsetcount,j++,
            (* Get label at (d.g.s)[[orbit[[j]]]] *)
              position=leastset[[j,2]];
              label=g[[leastset[[j,1]]]];
              orbitlabel=g[[position]];

              Debug@Print["Second pass: Processing least element with label ",label," found in configuration ",
                confignumber," at slot ",leastset[[j,1]]," originating from orbit point ",leastset[[j,2]]];

              (* First check whether label belongs to a previously-visited subgroups entry *)
              If[subgroups[[position]]!=0,
                If[visitedsyms[[Abs@subgroups[[position]]]]==0,
                  (* Unvisited symmetry group; mark as visited *)
                  (visitedsyms[[Abs@subgroups[[position]]]]=1),

                  (* Else, visited symmetry group; check whether to skip loop iteration *)
                  (Debug@Print["Label ",orbitlabel," belongs to previously-visited symmetry group ",
                    subgroups[[position]],"; skipping to next label"];

                  Continue[])
                ]];

              (* Next we need to implement dummy swap *)
              d=id;

              (* If we have an extra symmetry, exchange label and orbitlabel directly *)
              (* Note: This is only the label swap; the slot swap happens later *)
              If[(symmetries[[sinvg[[label]]]]!=0)&&(label!=orbitlabel),
              (* Check for the sign *)
                (If[symmetries[[sinvg[[label]]]]>0,
                  d[[{label,orbitlabel}]]=d[[{orbitlabel,label}]],
                  d[[{label,orbitlabel,-1,-2}]]=d[[{orbitlabel,label,-2,-1}]]];
                Debug@Print["Label symmetry from extra symmetry ",symmetries[[sinvg[[label]]]],":  Swap generator: ",d]),

              (* Otherwise, find the ordinary dummy swap that maps least to label *)

              (* Find the necessary dummy swap in label space *)
                (Switch[groups[[label]],
                (* Same component indices, completely symmetric *)
                  1,
                    (d[[{least,label}]]=d[[{label,least}]];
                    Debug@Print["Label symmetry 1:  Swap generator: ",d];
                    Null),

                (* Dummy indices with symmetric metric *)
                  2,
                    (If[OddQ[label-least],pair=label-1,pair=label];
                    If[pair!=least,
                      d[[{least,least+1,pair,pair+1}]]=d[[{pair,pair+1,least,least+1}]]
                    ];
                    If[pair!=label,
                      d[[{pair,label}]]=d[[{label,pair}]]
                    ];
                    Debug@Print["Label symmetry 2:  Swap generator ",d];
                    Null),

                (* Dummy indices with antisymmetric metric *)
                  -2,
                    (If[OddQ[label-least],pair=label-1,pair=label];
                    If[pair!=least,
                      d[[{least,least+1,pair,pair+1}]]=d[[{pair,pair+1,least,least+1}]]
                    ];
                    If[pair!=label,
                      d[[{pair,label,-2,-1}]]=d[[{label,pair,-1,-2}]]
                    ];
                    Debug@Print["Label symmetry -2:  Swap generator ",d];
                    Null),

                (* Lower dummy indices with no metric *)
                  3,
                    (d[[{least,least+1,label,label+1}]]=d[[{label,label+1,least,least+1}]];
                    Debug@Print["Label symmetry 3:  Swap generator ",d];
                    Null),

                (* Upper dummy indices with no metric *)
                  4,
                    (d[[{least-1,least,label-1,label}]]=d[[{label-1,label,least-1,least}]];
                    Debug@Print["Label symmetry 4:  Swap generator ",d];
                    Null),

                (* Otherwise, do nothing *)
                  _,Null
                ])
              ]; (* End If symmetries *)

              (* We need to add a new entry to nextconfigs *)
              nextconfigcount++;

              (* For testing:  Quit if we get too many configs *)
              Debug@If[nextconfigcount>50,Abort[]];

              (* Check if we need to allocate more space *)
              If[nextconfigcount>nextarraysize,
                nextconfigs=Join[nextconfigs,nextarrayincrement];
                nextarraysize+=length];

              (* Get the slot symmetry that brings us to this orbit point *)
              If[tree==0,s=id,
                s=Macro@cosetRep[slotdata,slotdata[[tree;;tree+1]],position,length]];

              Debug@Print["Slot symmetry which brings orbit slot ",position," to slot ",slot," is ",s];

              (* Add new entry to nextconfigss *)
              (* Note: label symmetry acts on the left, slot symmetry acts on the right *)
              nextconfigs[[nextconfigcount]]=
                  {d[[configs[[confignumber,1,s]]]],configs[[confignumber,2,s]]};

              Debug@Print["New entry added to nextconfigs: {g,s} = ",MatrixForm@nextconfigs[[nextconfigcount]]];

            (* Now move on to next element in leastset *)
            ]; (* End For j *)
          ]; (* End While i *)

          (*********************************************)
          (*** Do last processing before next slot *****)
          (*********************************************)

          (* We have finished using the values array, now we can update it to reflect that the selected label
            (and possibly its dummy partner) can no longer be exchanged *)
          Switch[groups[[least]],
          (* Component indices with same label *)
            1,
              (groups[[least]]=0;
              i=least+1;
              While[i<=length&&values[[i]]==least,
                values[[i]]++;
                i++]),

          (* Dummy indices with symmetric metric *)
            2,
              (groups[[least]]=groups[[least+1]]=0;
              values[[least+1]]++;
              i=least+2;
              While[i<=length&&values[[i]]==least,
                values[[i]]+=2;
                i++]),

          (* Dummy indices with antisymmetric metric *)
            -2,
              (groups[[least]]=groups[[least+1]]=0;
              values[[least+1]]++;
              i=least+2;
              While[i<=length&&values[[i]]==least,
                values[[i]]+=2;
                i++]),

          (* Lower dummy indices with no metric *)
            3,
              (groups[[least]]=groups[[least+1]]=0;
              i=least+2;
              While[i<=length&&values[[i]]==least,
                values[[i]]+=2;
                i+=2];
              i=least+3;
              While[i<=length&&values[[i]]==least+1,
                values[[i]]+=2;
                i+=2]),

          (* Upper dummy indices with no metric *)
            4,
              (groups[[least-1]]=groups[[least]]=0;
              i=least+1;
              While[i<=length&&values[[i]]==least-1,
                values[[i]]+=2;
                i+=2];
              i=least+2;
              While[i<=length&&values[[i]]==least,
                values[[i]]+=2;
                i+=2]),

          (* Otherwise, no update is needed *)
            _,Null];

          Debug@Print["Values:  ",values,"\nGroups:  ",groups,"\nSymmetries:  ",symmetries];

          (* Copy the sorted union of the nextconfigs into configs *)
          (* Sort order doesn't matter here, just makes it easier to detect duplicates/zero *)
          configs=Union[nextconfigs[[1;;nextconfigcount]]];
          configcount=Length[configs];

          (* Remove any remaining duplicates *)
          configs=Macro@removeDuplicates[configs,configcount,length];
          configcount=Length[configs];

          Debug@Print["The full configuration set is now:\n",MatrixForm/@configs];

          (* Check if we have zero *)
          zeroq=Macro@zeroConfigurationQ[configs,configcount,length];
          If[zeroq,Throw[Null]];

          (* Reset next config count *)
          nextconfigcount=0;

          (* Ready to repeat on next slot *)
          Null
        ] (* End For slots *)
      ]; (* End Catch *)

      (*********************************************)
      (***** End of slot loop: Return **************)
      (*********************************************)

      (* If zero, return list of zeros.  Otherwise, return the appropriate configuration *)
      If[zeroq,
        finalconfig=Array[0&,length],
        finalconfig=configs[[1,1]]];

      (* Return configuration *)
      finalconfig
    ],
  (* For now keep this in the virtual machine.  But consider compilation to bare metal! *)
    CompilationTarget->"C",RuntimeOptions->"Speed"
  ], (* End Compile *)
  Debug->False
]; (* End Meta *)





(* Haven't bothered making anything private *)
Begin["`Private`"]

End[] (* `Private` *)

EndPackage[]