Begin["`Private`"]; 
IGFs = {}; 
rulelist = {}; 
gfs = {}; solgf = {}; eom={};SuoEOM={};
preservelist = {}; 
sumlist = {};   (* sub scripts for summation (dummy ones) *)
GFnames={};
selfenergyrep={};
SelfEnergy={};  
GammaEnergy={};
acGFnames={};
acGFsol={};
closedsol={};
connectionlist={};  (* stores indices of each time-ordered gf *)
final={};  (* indices for "final" (exact) gf's *)
trunclist={};  (* { { {op1,op2,op3,...},total # of them},  {{ ol1,ol2,...}, # } , ... }  *)
category={};
oriNRIGF=0;
ETP={};
graph={};
interparam={};
CC={};  (* \:683c\:5f0f\:4e3a\:ff1a { { {t1,t2}, {t1star,t2star} }, { .... } } *)
plainCC={};
TBS={};  (* to be solved *)
TS={};   (* to be solved self-consistently *)
SC={};   (* single corr *)
Ling={"_",0,0,0};   (* \:77e9\:9635\:7684\:96f6\:5143 *)
II={"I",0,0,0};    (* \:77e9\:9635\:7684\:5355\:4f4d\:9635 *)
M={};
L={};
EnergySymbol=0;

Print["SymGF - Symbolic Green's Function"];
Print["Feng Zimin and Guo Hong\nPhysics, McGill"];
Print["2012-April-15"];
Print["Please make sure that this is a new Mathematica session !!!"]
Print["Report bugs or comments to ziminf@physics.mcgill.ca or guo@physics.mcgill.ca"]


teom[]:=SuoEOM
tm[]:=M

poletype={};  (* this list should have the same length as IGFs, for now this branch is paused. *)
Needs["NumericalCalculus`"];

tempo=0; (* to be deleted when debug finishes. *)

SetSingleCorr[a_List]:=Module[{},SC=a; ]

ResInto[cont_,sl_,w_]:=Module[{},
	Print[cont];
	Print[sl];
	Print[w];
	Abort[]
]
ResInto[___]:=Print["gaocuoda"];

PhysicalArgument[u_]:=Module[{ss,isoincore,i,j},   (* this physical argument doesn't work as it totally cuts off the U-effect *)
	ss=Select[IGFs,!FreeQ[#[[1]],u] & ] [[All,2]];
Print["elim ",ss];
	For[i=1,i<=Length[solgf],i++,
	Print[" ** ",i];
		If[Head[solgf[[i,3]] ] === Plus,
			solgf[[i,3]]=List@@solgf[[i,3]];
			For[j=1,j<=Length[solgf[[i,3]] ],j++,
				isoincore=Cases[solgf[[i,3,j]],_UnderBar];
				If[isoincore=!={},
					If[!FreeQ[ss,purepattern[ isoincore[[1]]  ]   ],
						solgf[[i,3,j]]=0;
						Print[j," set to 0 for ",isoincore];
					];
				];
			];
			solgf[[i,3]]=Plus@@solgf[[i,3]];
		,
			(* just one term *)
			isoincore=Cases[solgf[[i,3]],_UnderBar];
			If[isoincore=!={},
				If[!FreeQ[ss,purepattern[ isoincore[[1]] ]  ],
					solgf[[i,3]]=0;
					Print["set to 0 for ",isoincore];
				];
			];
		];
	];
]

SErep[]:=Module[{kkkkk,i,ss,sub,ret={}},
	(* this module is only for single level, if not, there could be real subs instead of stealth subs only. *)
	For[i=1,i<=Length[SelfEnergy],i++,
		ss=stealthsub[SelfEnergy[[i,2]] ];
		sub=subs[SelfEnergy[[i,2]] ];
		AppendTo[ret,(SelfEnergy[[i,2]]/.(Table[ ss[[j]] -> (Pattern[kkkkk,Blank[] ] /. kkkkk->ss[[j]] ),{j,Length[ss] } ] ~ Join ~
				Table[ sub[[j]] -> (Pattern[kkkkk,Blank[] ] /. kkkkk->sub[[j]] ),{j,Length[sub] } ] ) )  ];
	];
	ret=Table[ret[[i]]->SelfEnergy[[i,1]],{i,Length[ret] } ];
	ret
]

ISOrep[w_]:=Module[{kkkkk,i,sub,ret={}},
	(* this module is only for single level, if not, there could be real subs instead of stealth subs only. *)
	For[i=1,i<=Length[IGFs],i++,
		sub=subs[IGFs[[i,2]] ];
		AppendTo[ret,(IGFs[[i,2]]/.( Table[ sub[[j]] -> (Pattern[kkkkk,Blank[] ] /. kkkkk->sub[[j]] ),{j,Length[sub] } ] ) )  ];
	];
	ret=Table[ret[[i]]->1/(w-IGFs[[i,1]] ),{i,Length[ret] } ];
	ret
]

ISOidx[gi_UnderBar]:=Module[{ret},
	ret=Position[IGFs,purepattern[gi] ];
	If[ret==={},
		Print["Error: ISO unrecognizable: ",gi];
		Abort[];
	];
	ret[[1,1]]
]

GFIiL[gf_OverBar]:=Module[{ret},
	ret=Position[SuoEOM[[All,1]] ,purepattern[gf] ] ;
	If[Length[ret]!=1,
		Print["Error: zero or multiple gf's in list"];
		Abort[]
	];
	ret[[1,1]]
]

FenLei[expr_Times, i_, j_] :=
    (* 还需当expr不是 “乘” 开头的情况。 *)
    Module[{cont = expr, ret = {{{}, {}}, {{}, {}}, {}}, ii, rem, t, ddx},
        
        (* ddx means diracdelta's for x, there should be no ddy *)
        ddx  = Cases[cont, _DiracDelta]; (* we don't consider more complicated situations (e-ph interaction) for now *)
        cont = expr /. Table[ddx[[k]] -> 1, {k, Length[ddx]}];
        rem  = cont;
        
        For[ii = 1, ii <= i, ii++,
            t = Select[cont, ! FreeQ[#, x[ii]] &];
            
            If[Length[Union[Cases[t, _x, Infinity]]] > 1,
                Print["non-factorizable:", cont, " in ", t];
                Abort[];
            ];
            
            rem /= t;
            AppendTo[ret[[1, 1]], t];
        ];
        
        If[ddx =!= {},
            ret[[1, 2]] = (Level[#, {-2}] & /@ ddx) /. x[a_] :> a;
        ];
        
        For[ii = 1, ii <= j, ii++,
            t = Select[cont, ! FreeQ[#, y[ii]] &];
            
            If[Length[Union[Cases[t, _y, Infinity]]] > 1,
                Print["non-factorizable:", cont, " in ", t];
                Abort[];
            ];
            
            rem /= t;
            AppendTo[ret[[2, 1]], t];
        ];
        
        ret[[2, 2]] = {};
        AppendTo[ret[[3]], rem];   (* ret[[3]]={X, { {}, {}, {}, ... }  }  *)
        ret
    ];

FenLei[expr_, 0, 0] := {"_", 0, 0, {{{}, {}, {expr, {}}}}};


FenPei[expr_Plus, subl_List, hang_Integer] :=
    Module[{i},
        For[i = 1, i <= Length[expr], i++,
            FenPei[expr[[i]], subl, hang];
        ];
    ];

FenPei[expr_, subl_List, hang_Integer] :=
    Module[{j, g, h, l, subr, sr, dd, cont, subll, dest},
        
        (* 假定大矩阵 M 是全局变量。subl 是左边格林函数的下标； 
           hang 是左边格林函数的行值。 *)
        
        If[! FreeQ[expr, _OverBar],
            
            subll = Table[subl[[i]] -> x[i], {i, Length[subl]}];
            (* Print[subll]; *)
            
            g    = GFiT[expr];
            cont = expr /. g -> 1;
            subr = subs[g] /. subll;
            
            h = Length[subl];
            l = Length[subr];
            
            sr  = Table[subr[[i]] -> y[i], {i, Length[subr]}];
            dd  = (Select[sr, #[[1, 0]] === x &] /. Rule -> List) /. {x[a_] :> a, y[a_] :> a};
            (* only responsible for artificially added diracdelta functions. *)
            
            cont = (cont /. subll) /. sr;
            (* Print["con ", cont, " ", h, " ", l];
               Print[sr]; *)
            
            dest = {"c", h, l, {FenLei[cont, h, l]}};
            AppendTo[dest[[4, 1, 3]], dd];
            (* Print[" res: ", dest] *)
            
            M[[hang, GFIiL[g]]] = dest
            ,
            (* 这是个常数 *)
            (* Print["jian li:", expr]; *)
            
            subll = Table[subl[[i]] -> x[i], {i, Length[subl]}];
            (* Print[subll]; *)
            
            subr = {};
            h    = Length[subl];
            l    = Length[subr];
            
            (* only responsible for artificially added diracdelta functions. *)
            cont = expr /. subll;
            (* Print["con ", cont, " ", h, " ", l];
               Print[sr]; *)
            
            dest = {"c", h, l, {FenLei[cont, h, l]}};
            (* Print[" res: ", dest]; *)
            
            AppendTo[dest[[4, 1, 3]], {}];
            (* Print[" res: ", dest] *)
            
            M[[hang, -1]] = dest
        ];
    ];


CreateMat[w_: w] := JianLi[w]


JianLi[w_: w] :=
    Module[{i, subl},
        EnergySymbol = w;
        M = Table[Ling, {Length[SuoEOM]}, {Length[SuoEOM] + 1}];
        
        For[i = 1, i <= Length[SuoEOM], i++,
            subl = subs[SuoEOM[[i, 1]]];
            FenPei[-SuoEOM[[i, 2]], subl, i];
            M[[i, i]] = II;
        ];
        
        Print["Matrix established."];
        M
    ]


Cheng[m1_List, m2_List] :=
    Module[{tmp},
        (* 乘法运算 *)

        Which[
            (* Identity-like matrix *)
            m2[[1]] === "I",
                tmp = m1,

            (* c × c *)
            m1[[1]] === "c" && m2[[1]] === "c",
                If[m1[[3]] =!= m2[[2]],
                    Print["dimensions don't match: ", m1, " and ", m2];
                    Abort[],
                    tmp = ChengCC[m1, m2]
                ],

            (* c × Ic *)
            m1[[1]] === "c" && m2[[1]] === "Ic",
                If[m2[[2]] =!= m2[[3]],
                    Print["non-square matrix with Ic symbol:", m2];
                    Abort[],
                    tmp = ChengCC[m1, m2];
                    tmp[[4]] = Join[tmp[[4]], m1[[4]]];
                ],

            (* Ic × c *)
            m1[[1]] === "Ic" && m2[[1]] === "c",
                If[m1[[2]] =!= m1[[3]],
                    Print["non-square matrix with Ic symbol:", m1];
                    Abort[],
                    tmp = ChengCC[m1, m2];
                    tmp[[4]] = Join[tmp[[4]], m2[[4]]];
                ],

            (* Otherwise: error *)
            True,
                Print["error: can't identify matrices:", m1, " or ", m2]
        ];

        (* Reduce / simplify structure list *)
        tmp[[4]] = HuaJian[tmp[[4]], m1[[2]], m2[[3]]];
        tmp
    ]


ChengCC[m1_List, m2_List] :=
{
    "c",
    m1[[2]],
    m2[[3]],
    Flatten[
        Table[
            ChengLL[m1[[4, i]], m2[[4, j]]],
            {i, Length[m1[[4]]]},
            {j, Length[m2[[4]]]}
        ],
        1
    ]
}


Yu6[y_List, s_List] :=
    Module[{i, xy = y, xs = s, t},
        (* reverse-direction version of Yu5 *)

        For[i = 1, i <= Length[xy], i++,
            If[(t = Intersection[xy[[i]], xs[[All, 1]]]) =!= {},
                t = Position[xs[[All, 1]], t[[1]]][[1, 1]];

                xs = xs ~Join~
                    Table[{xy[[i, j]], xs[[t, 2]]}, {j, Length[xy[[i]]]}];

                xs = Delete[xs, t];
                xy = Delete[xy, i];
                i--;
            ];
        ];

        {xy, xs}
    ]


Yu5[y_List, e_List] :=
    Module[{i, xy = y, xe = e, t},
        (* see manuscript *)

        For[i = 1, i <= Length[xy], i++,
            If[(t = Intersection[xy[[i]], xe[[All, 2]]]) =!= {},
                t = Position[xe[[All, 2]], t[[1]]][[1, 1]];

                xe = xe ~Join~
                    Table[{xe[[t, 1]], xy[[i, j]]}, {j, Length[xy[[i]]]}];

                xe = Delete[xe, t];
                xy = Delete[xy, i];
                i--;
            ];
        ];

        {xy, xe}
    ]


Lian[e_List, s_List] :=
    Module[{i, t, xe = e, xs = s, k = {}},
        For[i = 1, i <= Length[xe], i++,
            If[(t = Position[xs[[All, 1]], xe[[i, 2]]]) =!= {},
                t = t[[1, 1]];
                AppendTo[k, {xe[[i, 1]], xe[[i, 2]], xs[[t, 2]]}];

                xe = Delete[xe, i];
                xs = Delete[xs, t];
                i--;
            ];
        ];

        {xe, xs, k}
    ]

ChengLL[l1_List,l2_List]:=Module[{a=Join[l1[[2,2]],l2[[1,2]] ],b=l1[[3,2]],c=l2[[3,2]],tmp,i,j,j2,m,k},
	tmp={l1[[1]],l2[[2]],{l1[[3,1]]l2[[3,1]] ,{} }  };
	{a,b}=Yu5[a,b];
	{a,c}=Yu6[a,c];
	{b,c,k}=Lian[b,c];
	For[i=1,i<=Length[l1[[2,1]] ],i++,
		Which[
			MemberQ[ b[[All,2]],i],
				j= b[[  Position[b[[All,2]],i][[1,1]],1]];
				tmp[[1,1,j]]*= (l1[[2,1,i]]/.y[i]->x[j])(l2[[1,1,i]]/.x[i]:>x[j]/;i!=j)
			,
			MemberQ[ c[[All,1]], i],
				j= c[[  Position[c[[All,1]],i][[1,1]],2]];
				tmp[[2,1,j]]*=(l1[[2,1,i]]/.y[i]:>y[j]/;j!=i) (l2[[1,1,i]]/.x[i]->y[j] )
			,
			MemberQ[k[[All,2]],i],
				j= k[[  Position[k[[All,2]],i][[1,1]],1]];
				tmp[[1,1,j]]*=(l2[[1,1,i]]/.x[i]:>x[j]/;j!=i)(l1[[2,1,i]]/.y[i]->x[j]);
				j2= k[[  Position[k[[All,2]],i][[1,1]],3]];
				(*tmp[[2,1,j]]*=l1[[2,1,i]]/.y[i]:>y[j]/;j!=i;*)
				tmp[[1,1,j2]]*=tmp[[2,1,j2]]/.y[i]->x[j];
				tmp[[2,1,j2]]=1;
			,
			MemberQ[Flatten[a],i],  (* i is in self-dirac's *)
				If[MemberQ[a[[All,1]],i],
					m=Position[a,i][[1,1]];
					tmp[[3,1]]*=SuoBing[Times@@(l1[[2,1,a[[m]] ]]) ,Times@@(l2[[1,1,a[[m]] ]])]
				]
			,
			True,
				tmp[[3,1]]*=SuoBing[(l1[[2,1,i]]) ,(l2[[1,1,i]] )]
		]
	];
	tmp[[3,2]]=k[[All,{1,3}]];
	tmp
]

Jian[m1_List,m2_List]:=Module[{ret=m1,tmp=m2},
	If[m1[[2]]!=m2[[2]]||m1[[3]]!=m2[[3]],
		Print["non-matching dimension of matrices:",m1 ," and ",m2];
		Abort[]
	];

	tmp[[4,All,3,1]]*=-1;
	ret[[4]]=ret[[4]]~Join~tmp[[4]] ;
	ret[[4]]=HuaJian[ret[[4]] ,m1[[2]],m1[[3]]   ];
	(*If[Length[ret[[4]]  ]>1,Print["jian cheng: ",ret]; ];*)
	ret
]

Jian[Ling,m2_List]:=Module[ {tmp=m2},
	tmp[[4,All,3,1]]*=-1;
	tmp
]

Jian[II,m2_List]:=Module[ {tmp=m2},
	tmp[[4,All,3,1]]*=-1;
	tmp[[1]]="Ic";
	tmp
]

YiYangX[l_List]:=Module[{i,tmp,ret={} ,p},
(* \:8fd4\:56de\:4e00\:6837\:7684\:4e1c\:897f\:7684\:5217\:8868\:ff0c\:4ee5\:53ca\:5bf9\:5e94\:7684\:4f4d\:7f6e *)
	For[i=1,i<=Length[l]-1,i++,
		If[ l[[i,1]]===l[[i+1,1]] && l[[i,3,2]]===l[[i+1,3,2]],
			p=Position[ l[[All,1]],l[[i,1]]  ][[All,1]];
	AppendTo[ret,{l[[i,1]],p }]
	]
	];
Union[ret]
]
YiYangY[l_List] :=
    Module[{i, tmp, ret = {}, p},
        (* 返回一样的东西的列表，以及对应的位置 *)
        For[i = 1, i <= Length[l] - 1, i++,
            If[ l[[i, 2]] === l[[i + 1, 2]] &&
                l[[i, 3, 2]] === l[[i + 1, 3, 2]],
                
                p = Position[l[[All, 2]], l[[i, 2]]][[All, 1]];
                AppendTo[ret, {l[[i, 2]], p}];
            ];
        ];
        Union[ret]
    ]


HeBingX[l_List, yy_List, dimen_] :=
    Module[{ret = {}, i, j, s},
        (* s 是无法化简的项 *)
        s = Complement[Range[Length[l]], Flatten[yy[[All, 2]]]];
        
        For[i = 1, i <= Length[s], i++,
            AppendTo[ret, l[[s[[i]]]]];
        ];
        
        For[i = 1, i <= Length[yy], i++,
            Which[
                dimen == 1,
                    AppendTo[
                        ret,
                        {
                            yy[[i, 1]],
                            {
                                {
                                    Plus @@ (
                                        Apply[
                                            Times,
                                            l[[yy[[i, 2]], 2, 1]],
                                            {1}
                                        ] * l[[yy[[i, 2]], 3, 1]]
                                    )
                                },
                                l[[yy[[i, 2, 1]], 2, 2]]
                            },
                            {1, l[[yy[[i, 2, 1]], 3, 2]]}
                        }
                    ],
                
                (* this proc fails if subs' length exceeds one *)
                
                dimen == 0,
                    AppendTo[
                        ret,
                        {
                            yy[[i, 1]],
                            {{}, {}},
                            {
                                Plus @@ (
                                    Apply[
                                        Times,
                                        l[[yy[[i, 2]], 2, 1]],
                                        {1}
                                    ] * l[[yy[[i, 2]], 3, 1]]
                                ),
                                l[[yy[[i, 2, 1]], 3, 2]]
                            }
                        }
                    ]
            ];
        ];
        
        {ret[[-1, 2, 1]], ret[[-1, 3, 1]]} =
            Fen[ret[[-1, 2, 1]], ret[[-1, 3, 1]], y];
        
        ret
    ]


HeBingY[l_List, yy_List, dimen_] :=
    Module[{ret = {}, i, j, s},
        (* s 是无法化简的项 *)
        s = Complement[Range[Length[l]], Flatten[yy[[All, 2]]]];
        
        For[i = 1, i <= Length[s], i++,
            AppendTo[ret, l[[s[[i]]]]];
        ];
        
        For[i = 1, i <= Length[yy], i++,
            Which[
                dimen == 1,
                    AppendTo[
                        ret,
                        {
                            {
                                {
                                    Plus @@ (
                                        Apply[
                                            Times,
                                            l[[yy[[i, 2]], 1, 1]],
                                            {1}
                                        ] * l[[yy[[i, 2]], 3, 1]]
                                    )
                                },
                                l[[yy[[i, 2, 1]], 1, 2]]
                            },
                            yy[[i, 1]],
                            {1, l[[yy[[i, 2, 1]], 3, 2]]}
                        }
                    ],
                
                (* this proc fails if subs' length exceeds one *)

                dimen == 0,
                    AppendTo[
                        ret,
                        {
                            {{}, {}},
                            yy[[i, 1]],
                            {
                                Plus @@ (
                                    Apply[
                                        Times,
                                        l[[yy[[i, 2]], 1, 1]],
                                        {1}
                                    ] * l[[yy[[i, 2]], 3, 1]]
                                ),
                                l[[yy[[i, 2, 1]], 3, 2]]
                            }
                        }
                    ]
            ];
        ];
        
        {ret[[-1, 1, 1]], ret[[-1, 3, 1]]} =
            Fen[ret[[-1, 1, 1]], ret[[-1, 3, 1]], x];
        
        ret
    ]


Fen[lb_List, onum_, v_] :=
    Module[{i, l = lb, num = onum, t},
        For[i = 1, i <= Length[l], i++,
            l[[i]] = Simplify[l[[i]]];
            
            Which[
                Head[l[[i]]] === Times,
                    t = Select[l[[i]], FreeQ[#, v[i]] &];
                    num *= t;
                    l[[i]] /= t,
                
                Head[l[[i]]] =!= Times,
                    If[FreeQ[l[[i]], v[i]],
                        num *= l[[i]];
                        l[[i]] = 1;
                    ]
            ];
        ];
        {l, num}
    ]


HuaJian[l_List, dx_, dy_] :=
    Module[{t, ret = l},
        ret = Sort[l, OrderedQ[{#1[[2]], #2[[2]]}] &];
        
        t = YiYangY[ret];
        If[t =!= {},
            ret = HeBingY[ret, t, dx];
        ];
        
        ret = Sort[ret];
        
        t = YiYangX[ret];
        If[t =!= {},
            ret = HeBingX[ret, t, dy];
        ];
        
        ret
    ]


xm[gi_UnderBar, ss_] :=
    (* when one of the subs of a gi or the sub of gi is summed,
       it can be replaced with a delta function *)
    Module[{ret, idx, fm, rep},
        idx = ISOidx[gi];
        fm  = IGFs[[idx, 1]] /. ISOsubsub[IGFs[[idx, 2]], gi];
        
        rep = Select[fm, ! FreeQ[#, ss] &];
        (* rep is the energy symbol that takes ss as its subs *)
        
        If[rep === 0,
            Print["no subscript ", ss, " found in ", gi, " => ", fm];
            Abort[];
        ];
        
        If[MatchQ[rep, Times[-1, _]],
            ret = -I π DiracDelta[EnergySymbol - fm + rep + ss],
            ret = -I π DiracDelta[EnergySymbol - fm + rep - ss]
        ];
        
        ret
    ]

SuoBing[t1_,t2_]:=Module[{cont,ret,p},
	cont=(t1 t2)/.{x->GlobalSummationScript,y->GlobalSummationScript};
	p=Position[ GammaEnergy[[All,1]] , cont ];
	If[ p=!={},
		ret=GammaEnergy[[ p[[1,1]], 2]]
	,
		AppendTo[GammaEnergy,{cont,Unique["\[CapitalGamma]"]} ];
		ret=GammaEnergy[[-1,2]]
	];
	ret
]
(*  \:8fd9\:91cc\:9700\:8981\:589e\:52a0\:5bf9\:5b9e\:90e8\:662f\:5426\:975e\:96f6\:7684\:5224\:65ad  *)
(*SuoBing[t1_,t2_]:=Module[{sl,j,gi,cont,deltaPool,sol,i,S},
cont=(t1 t2)/.{x->S,y->S};
If[Head[cont]=!=Times && Head[cont]=!=Symbol,
Print["in function SuoBing, the cont may be illegal.",cont];
];
sl=Union[ Cases[cont,_S,\[Infinity]]  ];
(*Print["in function contraction:",sl];*)
Print[cont];
Print[cont/.S[_]->_];
Abort[];
For[j=1,j<=Length[sl],j++,
gi=Cases[cont,UnderBar [a_[___,sl[[j]] ,___    ] ]      ,\[Infinity]      ];
If[Length[gi]!=1 || (Length[gi]==1&&! FreeQ[Cases[cont   ,Power[___,_],\[Infinity]],gi[[1]]  ]),
(* gi\:591a\:4e8e\:4e00\:4e2a\:ff0c\:6216\:867d\:7136\:4e00\:4e2agi\:4f46\:5728\:5206\:6bcd\:4e0a\:6216\:6709\:5e42\:3002 *)
If[(Length[gi]==1&&! FreeQ[Cases[cont   ,Power[___,_],\[Infinity]],gi[[1]]  ]),
Print["pay attention to this new pattern:",cont];
];
cont=ResInto[cont,sl[[j]],EnergySymbol] ;
,  (* only one gi, can use direct replace *)
gi=gi[[1]];
cont=cont/gi*xm[gi,sl[[j]]];
deltaPool=Select[Cases[cont,_DiracDelta,\[Infinity]],!FreeQ[#,sl[[j]]  ]&];  (*dirad *)
sol=Solve[ deltaPool[[1,1]]==0,sl[[j]]  ] [[1,1]];
If[ !FreeQ[sol,Root],Print["WTH !!",deltaPool]; Abort[]  ];
cont=Simplify[(cont/.deltaPool[[1]]->1)  ]/.sol;
];

];
If[!FreeQ[cont,DiracDelta[0]  ],Print[cont," now screwed!! "];
Print[cont," \n",deltaPool];
Abort[]   
];
cont
]
*)
KeNi[m_List] :=
    Module[{ret = True, i},
        If[m[[2]] =!= m[[3]] || m[[1]] =!= "Ic",
            ret = False,
            For[i = 1, i <= Length[m[[4]]], i++,
                If[m[[4, i, 1, 2]] =!= {} || m[[4, i, 2, 2]] =!= {},
                    ret = False
                ]
            ]
        ];
        (* 还需要查delta函数。 *)
        ret
    ]


QingKuang[m_] :=
    Module[{d = 0, f = 0, i},
        (* m[[4]] *)
        If[m[[2]] == 0,
            1 (* 1、这个矩阵只是一个数； *),
            For[i = 1, i <= Length[m[[4]]], i++,
                If[m[[4, i, 3, 2]] === {},
                    f++,
                    d++
                ]
            ];
            Which[
                d == 0 && f == 1,
                    2 (* 2、没有对角部分，一个分离变量的部分； *),
                d > 0 && f == 0,
                    3 (* 3、只有对角部分，没有分离变量部分； *),
                d > 0 && f == 1,
                    4 (* 4、既有对角部分，也有一个分离变量的部分； *),
                d == 0 && f > 1,
                    5 (* 5、没有对角部分，但有多个分离变量部分。*),
                d > 0 && f > 1,
                    6 (* 6、有一个对角部分，也有多个分离变量部分。*)
            ]
        ]
    ]


Ni[II] := II


Ni[m_List] :=
    Module[{ret, t1, t2},
        (* Print["inverting:", m]; *)
        If[! KeNi[m],
            Print["not a invertible matrix:", m];
            Abort[];
        ];
        (*
        对将要取逆的矩阵mat，分以下几种情况：
        1、这个矩阵只是一个数；
        2、没有对角部分，一个分离变量的部分；
        3、只有对角部分，没有分离变量的部分；
        4、既有对角部分，也有一个分离变量的部分；
        5、没有对角部分，但有多个分离变量的部分。
        6、有一个对角部分，也有多个分离变量的部分。
          （尚未遇到后两种情况，如果分离变量部分可以继续因式分解，则应继续分解，否则算法失效。）
        *)
        Switch[QingKuang[m],
            1,
                (* 1、这个矩阵只是一个数； *)
                (* wrong format!!! *)
                ret = {
                    "c",
                    0,
                    0,
                    {
                        {
                            {{}, {}},
                            {{}, {}},
                            {1/(1 + m[[4, 1, 3, 1]]), {}}
                        }
                    }
                },  (* change!!!!! *)

            2,
                (* 2、没有对角部分，一个分离变量的部分； *)
                ret = m;
                ret[[4, 1, 3, 1]] *= -1/(1 + ret[[4, 1, 3, 1]] SuoBing[Times @@ ret[[4, 1, 1, 1]],
                                                                         Times @@ ret[[4, 1, 2, 1]]]),

            3,
                (* 3、只有对角部分，没有分离变量的部分； *)
                (* 如果深度大于1就糟了。 *)
                If[m[[2]] > 1 || Length[m[[4]]] > 1,
                    Print["zao le"];
                    Print[m];
                    Abort[];
                ];
                ret = {
                    "c",
                    m[[2]],
                    m[[3]],
                    {{
                        {
                            1/(1 + m[[4, 1, 3, 1]] m[[4, 1, 1, 1]] (m[[4, 1, 2, 1]] /. y[a_] -> x[a])),
                            {}
                        },
                        {Table[1, {m[[3]]}], {}},
                        {1, m[[4, 1, 3, 2]]}
                    }}
                },

            4,
                (* 4、既有对角部分，也有一个分离变量的部分； *)
                (* 若A为一个对角阵，则 (I + A + B)^-1 = (I + (I + A)^-1 B)^-1 (I + A)^-1。
                   程序中， = (I + A)^-1； = B。 *)
                t1 = Ni[{m[[1]], m[[2]], m[[3]], Select[m[[4]], #[[3, 2]] =!= {} &]}];
                (* Print["yi ni:", t1]; *)
                (* Print["multi:", {"c", m[[2]], m[[3]], Select[m[[4]], #[[3, 2]] === {} &]}]; *)
                t2 = Cheng[t1, {"c", m[[2]], m[[3]], Select[m[[4]], #[[3, 2]] === {} &]}];
                t2[[1]] = "Ic";  (* 因为前面加了一个I *)
                (* Print["t2:", t2]; *)
                ret = Cheng[Ni[t2], t1],

            5,
                (* 5、没有对角部分，但有多个分离变量的部分。
                   （尚未遇到此情况，如果分离变量部分可以继续因式分解，则应继续分解，否则算法失效。） *)
                Print[5];
                Print[m];
                Abort[],

            6,
                (* 6、有一个对角部分，也有多个分离变量的部分。
                   （尚未遇到此情况，如果分离变量部分可以继续因式分解，则应继续分解，否则算法失效。） *)
                Print[6];
                Print[m];
                Abort[]
        ];
        ret
    ]

GaussElim[]:=Module[{p,h,l,t,temp},
	Print["Gaussian Elimination of ",Length[M],"x",Length[M]+1," matrix.\nDoing row:"];
	t=TimeUsed[];
	Monitor[
		For[p=Length[M],p>0,p--,
			L[[1]]=Ni[ M[[p,p]] ];  (* Ni=Inverse *)
			For[h=p-1,h>0,h--,
				If[M[[h,p]]===Ling,Continue[] ];
				L[[2]]=Cheng[M[[h,p]],L[[1]]   ];
				For[l=p-1,l>0,l--,
					If[M[[p,l]]===Ling,Continue[] ];
					L[[3]]=Cheng[ L[[2]], M[[p,l]]  ];
					M[[h,l]]=Jian[ M[[h,l]] , L[[3]]   ];
				];(* l *)
				If[M[[p,Length[M]+1]]=!=Ling,
					L[[3]]=Cheng[ L[[2]], M[[p,Length[M]+1]]  ];
					M[[h,Length[M]+1]]=Jian[ M[[h,Length[M]+1]] , L[[3]]   ]; 
				];
				M[[h,p]]=Ling; (* not using it is equivalent to setting it to zero *)
			]; (* h *)
		],  (* p *)
		p
	]; (* monitoring p*)
	Print["Finished in ",TimeUsed[]-t," seconds."];
	M
]

aussXQ[] :=
    Module[{p, h, l},
        
        For[p = Length[M], p > 0, p--,
            
            Print[p];
            L[[1]] = Ni[M[[p, p]]];  (* Ni = Inverse *)
            Print[p];
            
            For[h = p - 1, h > 0, h--,
                
                If[M[[h, p]] === Ling, Continue[]];
                
                If[p == 70, Print["h: ", h];];
                If[p == 70 && h == 67,
                    Print["L1:", L[[1]]];
                    Print["M:", M[[h, p]]];
                ];
                
                L[[2]] = Cheng[M[[h, p]], L[[1]]];
                
                If[p == 70 && h == 67, Print["tic"];];
                
                For[l = p - 1, l > 0, l--,
                    
                    If[M[[p, l]] === Ling, Continue[]];
                    
                    If[p == 70 && h == 67, Print["tic2 ", l];];
                    
                    L[[3]] = Cheng[L[[2]], M[[p, l]]];
                    
                    If[p == 70 && h == 67, Print["tic3 ", l];];
                    
                    M[[h, l]] = Jian[M[[h, l]], L[[3]]];
                    
                    If[p == 70 && h == 67, Print["tic4 ", l];];
                ];  (* l *)
                
                If[M[[p, Length[M] + 1]] =!= Ling,
                    L[[3]] = Cheng[L[[2]], M[[p, Length[M] + 1]]];
                    M[[h, Length[M] + 1]] =
                        Jian[M[[h, Length[M] + 1]], L[[3]]];
                ];
                
                (* not using it is equivalent to setting it to zero *)
                M[[h, p]] = Ling;
            ];  (* h *)
        ];  (* p *)
        
        M
    ]



(* ========================================================== \:5b59\:5e86\:5cf0\:89e3 ============================================================ *)
CondIter[]:=sunqfjie[]
sunqfjie[]:=Module[{tim,i,fe={}},
	(* start with eom[[1]] *)
	
	(* find a term with coulping constant multiplied with a GF, a lot things, only U and -1 are exception (?)  *)

	(* for each of the terms, (in which there should be only one GF), find the corresponding eom, 
	 use that eom to generate (subs) the right eom with multiplier. *)

	(* check the rhs of that new eom. if there is a pair of CC, then all the related iso-gf and that pair forms a SE. could judge by subs and ??
		but should be ok. later can be judged by type ? i think subs will be enough. *)
	
	(* keep that new eom and do....... *)
	tim=TimeUsed[];
	TBS={1};
	i=1;
	While[i<=Length[TBS],
		Print["Doing ",i," from ",TBS];
		TS={};
		AppendTo[fe,GFnames[[ TBS[[i]] ]] ==kaca[TBS[[i]],{},1,{}]  ];
		i++;
	];
	Print["finally ",fe," with ",GFnames[[ TBS ]] ];
(*	Print["SE: ",SelfEnergy];*)
	Print["Finished in ",TimeUsed[]-tim," seconds."];
]

listify[expr_Times]:=Module[{tmp,pos},
	tmp=List@@expr;
	For[pos=Position[tmp,_Power],Length[pos]>0,pos=Position[tmp,_Power],
		tmp[[pos[[1,1]] ]]=Table[tmp[[pos[[1,1]],1]],{tmp[[pos[[1,1]],2]] } ];
	];
	tmp//Flatten
]
listify[expr_]:=Module[{},Print["na lai de??? "];Abort[];]

(* \:610f\:601d\:5c31\:662f\:8bf4\:8981\:628a\:96be\:770b\:7684\:683c\:6797\:51fd\:6570\:5494\:5693\:4e86\:ff01*)
kaca[GFind_Integer, pathway_List, multiplier_, replist_] :=
    Module[{i, j, curreom, gfidx, gfform, recent, lhs, baksum},
        
        curreom = (eom[[GFind]]*multiplier /. replist) // ExpandAll;
        lhs     = (GFnames[[GFind]] /. replist)*multiplier;
        (* Print["   kaca : ", GFind, "  ", lhs, " == ", curreom, "  ", pathway, "    "]; *)
        
        Switch[curreom,
            
            _Plus,
                curreom = List @@ curreom;  
                (* 必须换成列表，否则做过计算以后有可能项与项之间的顺序可能（肯定）会变！第二次犯这种傻了！！ *)
                (* Print[GFind, "  ", curreom]; *)
                
                For[i = 1, i <= Length[curreom], i++,
                    
                    (* there should be no subs in diracdelta that is also in lhs *)
                    If[! FreeQ[curreom[[i]], DiracDelta],
                        backsum = sumlist;
                        sumlist = Complement[sumlist, subs[lhs]];
                        curreom[[i]] = grab3[curreom[[i]]];
                        sumlist = backsum;
                    ];  (* may change grab3, or just here; may cause trouble *)
                    
                    (* Print["----- term ", i, " of ", GFind, "  ", curreom[[i]]]; *)
                    
                    recent = MiT[curreom[[i]]]/multiplier;
                    curreom[[i]] = grasp[lhs, recent, curreom[[i]]];   
                    (* 还没做下标代替，要做。 *)
                    (* Print["grasped into: ", curreom[[i]], " lhs: ", lhs]; *)
                    
                    gfidx  = GFIiT[curreom[[i]]];
                    gfform = GFiT[curreom[[i]]];
                    
                    If[Length[gfform] > 1,
                        Print["Error: multiple of GF's found in term ", curreom[[i]]];
                        Abort[];
                    ];
                    
                    If[gfidx > 0,
                        If[CCinTerm[curreom[[i]]],
                            
                            If[! MemberQ[pathway, gfidx],
                                (* Print["passing ", i, " of ", GFind, "  ", MiT[curreom[[i]]], "   ", multiplier]; *)
                                curreom[[i]] =
                                    curreom[[i]]/MiT[curreom[[i]]]/gfform *
                                    kaca[
                                        gfidx,
                                        pathway ~Join~ {GFind},
                                        MiT[curreom[[i]]],
                                        GFTOsubsub[GFnames[[gfidx]], gfform]
                                    ];
                                (* Print["now ", i, "'th term of GF ", GFind, " = ", curreom[[i]]];
                                   Print["and totally GF", GFind, " = ", curreom]; *)
                                ,
                                TS = Union[TS, {gfidx}];
                                (* Print["TS: ", TS];
                                   Print["path: ", pathway, "  idx: ", gfidx]; *)
                            ],
                            
                            If[FreeQ[TBS, gfidx],
                                AppendTo[TBS, gfidx]
                            ];
                            (* 没有就好 *)
                        ];
                    ,
                        Print["Temp: ", curreom[[i]], " has no GF."];
                    ];
                    
                    If[! FreeQ[curreom[[i]], DiracDelta],
                        (* have to do it again, as the lhs' could be annoying *)
                        backsum = sumlist;
                        sumlist = Complement[sumlist, subs[lhs]];
                        curreom[[i]] = grab3[curreom[[i]]];
                        sumlist = backsum;
                    ];  (* may change grab3, or just here; may cause trouble *)
                    
                    If[Head[curreom[[i]]] === Plus,
                        curreom[[i]] = List @@ curreom[[i]];
                        
                        For[j = 1, j <= Length[curreom[[i]]], j++,
                            recent = MiT[curreom[[i, j]]]/multiplier;
                            curreom[[i, j]] =
                                grasp[lhs, recent, curreom[[i, j]]];   
                            (* 还没做下标代替，要做。 *)
                        ];
                        
                        curreom[[i]] = Plus @@ curreom[[i]];
                    ,
                        (* i assume curreom[[i]] is still one term *)
                        recent = MiT[curreom[[i]]]/multiplier;
                        curreom[[i]] = grasp[lhs, recent, curreom[[i]]];   
                        (* 还没做下标代替，要做。 *)
                    ];
                ];
                
                curreom = Plus @@ curreom,
            
            _Times,
                If[! FreeQ[curreom, DiracDelta],
                    backsum = sumlist;
                    sumlist = Complement[sumlist, subs[lhs]];
                    curreom = grab3[curreom];
                    sumlist = backsum;
                ];  (* may change grab3, or just here; may cause trouble *)
                
                (* Print["the only term of ", GFind, "  ", curreom]; *)
                
                recent  = MiT[curreom]/multiplier;
                curreom = grasp[lhs, recent, curreom];   
                (* 还没做下标代替，要做。 *)
                (* Print["grasped into ", curreom]; *)
                
                gfidx  = GFIiT[curreom];
                gfform = GFiT[curreom];
                
                If[Length[gfform] > 1,
                    Print["Error: multiple of GF's found in term ", curreom];
                    Abort[];
                ];
                
                If[gfidx > 0,
                    If[CCinTerm[curreom],
                        
                        If[! MemberQ[pathway, gfidx],
                            curreom =
                                curreom/MiT[curreom]/GFiT[curreom] *
                                kaca[
                                    gfidx,
                                    pathway ~Join~ {GFind},
                                    MiT[curreom],
                                    GFTOsubsub[GFnames[[gfidx]], gfform]
                                ];
                        ,
                            TS = Union[TS, {gfidx}];
                        ];
                    ,
                        If[FreeQ[TBS, gfidx],
                            AppendTo[TBS, gfidx]
                        ];
                        (* 没有就好 *)
                    ];
                ,
                    Print["Temp: ", curreom, " has no GF."];
                ];
                
                If[! FreeQ[curreom, DiracDelta],
                    backsum = sumlist;
                    sumlist = Complement[sumlist, subs[lhs]];
                    curreom = grab3[curreom];
                    sumlist = backsum;
                ];  (* may change grab3, or just here; may cause trouble *)
                
                If[Head[curreom] === Plus,
                    curreom = List @@ curreom;
                    For[j = 1, j <= Length[curreom], j++,
                        recent  = MiT[curreom[[j]]]/multiplier;
                        curreom[[j]] =
                            grasp[lhs, recent, curreom[[j]]];   
                        (* 还没做下标代替，要做。 *)
                    ];
                    curreom = Plus @@ curreom;
                ,
                    (* i assume curreom is still one term *)
                    recent  = MiT[curreom]/multiplier;
                    curreom = grasp[lhs, recent, curreom];   
                    (* 还没做下标代替，要做。 *)
                ],
            
            _,
                Print["Error: Unknown expression type: ", curreom];
                Abort[];
        ];
        
        If[MemberQ[TS, GFind],
            (* 包含自己的话需要先解了它 *)
            (* Print["**", GFind, " ", multiplier, " ", GFnames[[GFind]] /. replist,
                     " \n  ", curreom, "  ", pathway, "  ", TS]; *)
            curreom = solveself[lhs, curreom];
        ];
        
        (* Print["   kaca : ", GFind, " ends with: ", lhs, " == ",
                 curreom // ExpandAll, "  ", pathway, "    "]; *)
        
        curreom // ExpandAll
    ]


solveself[lhs_, rhs_Plus] :=
    Module[{redo = 1, i, fm, trhs = rhs, oneminus = 0, rec = {}, u, poly, cd,
            left, ret = 0, ab = 0, fm2},

        While[redo == 1,
            redo = 0;
            trhs = List @@ trhs;
            fm   = GFiT[lhs];

            For[i = 1, i <= Length[trhs], i++,
                If[! FreeQ[trhs[[i]], fm],
                    oneminus += trhs[[i]]/lhs;
                    (* If[!FreeQ[oneminus,Power],
                           Print["bu de liao le!!!!\n",lhs," == ",rhs,"\n",trhs];
                           Abort[];]; *)
                    trhs[[i]] = 0;
                ,
                    (* ok here means trhs[[i]] do not have fm *)
                    (* may cause infinite iteration. *)
                    If[! FreeQ[trhs[[i]], purepattern[fm]],
                        (* if it reaches here then it means this GF changed subs, have to replace dummy subs *)
                        Print[" dummy vars "];
                        (* trhs[[i]]=kaca[GFIiT[fm],{},trhs[[i]]/GFiT[trhs[[i]] ],GFTOsubsub[GFnames[[GFIiT[fm] ]],fm] ]; *)
                        trhs[[i]] =
                            ExpandAll[diedaiTOsky[trhs[[i]], {GFIiT[trhs[[i]]]}]];

                        If[! FreeQ[trhs[[i]], DiracDelta],
                            backsum = sumlist;
                            sumlist = Complement[sumlist, subs[lhs]];
                            trhs[[i]] = grab3[trhs[[i]]];
                            sumlist = backsum;
                        ];  (* may change grab3, or just here; may cause trouble *)

                        redo = 1;
                    ]
                ];
            ];

            If[! FreeQ[trhs, Power[_, -1]],
                Print["internal error: shouldn't have division ", trhs];
            ];

            trhs = Plus @@ trhs;
        ];

        (* here we can grasp them again, as we fucking need it! *)
        (* ideally, or i think, the relationship between a GF and another GF should be not random at all.
           if GF1 = tl[k] GF2, then there should be no other equations like GF1 = t1d GF2.
           when dealing with devrim's thesis, we met the case where multipliers of self-energies differ. *)

        If[Head[trhs] =!= Plus,
            poly = trhs;
            cd   = Times @@ Cases[poly, _OverTilde];
            left = poly/cd;
            fm2  = GammaEnergySymbol[lhs, cd, 1 - oneminus]*left;
            If[Length[GammaEnergy] == 62,
                Print["ge 1 ", lhs, "  ", cd, "  ", oneminus];
            ];
            ret = grasp[1, fm2, fm2];
        ,
            equaltime = Select[trhs, GFIiT[#] == 0 &];

            For[i = 1, i <= Length[trhs], i++,
                AppendTo[
                    rec,
                    {GFIiT[trhs[[i]]], CCprofile[trhs[[i]]], GFiT[trhs[[i]]]}
                ];
            ];

            u = Union[rec[[All, 1]]];

            For[i = 1, i <= Length[u], i++,
                If[u[[i]] != 0 &&
                   Length[
                     Union[
                       Select[rec, #[[1]] == u[[i]] &][[All, 2]]
                     ]
                   ] != 1,
                    Print["internal error: uneven CC in self-consistent solution of eq. ",
                          lhs, " == ", trhs " == ", rhs];
                    Print[rec];
                    Print[u];
                    Print[u[[i]]];
                    ab = 1;
                    (* Abort[]; *)
                ];
            ];  (* the above makes sure the assumption of equaty of CC's *)

            (* CC's may still have different subs, this should be avoided; run it for now.
               if that's necessary we'll add it in the future. *)

            (* Print[" ~~~~~~~~~~~~rec~~~~~~~~~~~~~ "];
               Print[TableForm[rec]]; *)

            (* take it for granted that all the non-self GF's have the same iso-gf's for now.
               when needed, blow~~ *)

            u = Union[rec[[All, 3]]];

            (* Print[u]; *)
            u = Cases[u, _OverBar];
            (* Print[u]; *)

            For[i = 1, i <= Length[u], i++,
                poly = Select[rhs, ! FreeQ[#, u[[i]]] &];
                (* Print[i, " ______ ", poly]; *)

                If[Head[poly] === Plus,
                    poly = Table[poly[[j]], {j, Length[poly]}];
                    (* Print[poly]; *)
                    cd   = PolynomialGCD[Sequence @@ poly];
                    left = cd;
                    (* Print[cd]; *)
                    cd   = Plus @@ (poly/cd);  
                    (* this is the numeritor that is to be defined within new SE *)
                    (* Print["new SE's numeritor: ", cd]; *)
                ,
                    (* if there is only one term that contains the desired GF, then.... *)
                    cd   = Times @@ Cases[poly, _OverTilde];
                    left = poly/cd;
                ];

                fm2 = GammaEnergySymbol[lhs, cd, 1 - oneminus]*left;
                (* If[Length[GammaEnergy]==62,
                      Print["ge 2 ",lhs,"  ",cd,"  ",oneminus, " ",fm2]; ]; *)
                ret += grasp[1, fm2, fm2];
            ];

            If[equaltime =!= 0,   (* to be deleted if we aren't using the original 'devrim' setup *)
                If[Head[equaltime] === Plus,
                    For[i = 1, i <= Length[equaltime], i++,
                        cd   = Times @@ Cases[equaltime[[i]], _OverTilde];
                        left = equaltime[[i]]/cd;
                        fm2  = GammaEnergySymbol[lhs, cd, 1 - oneminus]*left;
                        If[Length[GammaEnergy] == 62,
                            Print["ge 3 ", equaltime, "  ", fm2];
                        ];
                        ret += grasp[1, fm2, fm2];
                    ]
                ,
                    cd   = Times @@ Cases[equaltime, _OverTilde];
                    left = equaltime/cd;
                    fm2  = GammaEnergySymbol[lhs, cd, 1 - oneminus]*left;
                    If[Length[GammaEnergy] == 62,
                        Print["ge 4 ", equaltime, "  ", fm2];
                    ];
                    ret += grasp[1, fm2, fm2];
                ];
            ];  (* equal time .*)

            tempo++;

            If[ab == 1,
                Print[tempo, "  ", ab];
                Abort[];
            ];
        ];

        If[! FreeQ[ret, purepattern[fm]],
            Print["internal error: ", fm, " not solved but should have...."];
            Abort[];
        ];

        ret
    ]

solveself[lhs_,rhs_]:=rhs



(*Module[{},Print["Error: incomprehensible equation ",lhs," == ",rhs];Abort[];]  *)

CCprofile[term_Times]:=Module[{ret={},i,tt},
	tt=listify[term];
	For[i=1,i<=Length[plainCC],i++,
		AppendTo[ret,Count[tt,purepattern[plainCC[[i]] ] ]   ];
	];
	ret
]

selfconsistent[gfidx_,rhs_Plus]:=Module[{i,ret=False},
	For[i=1,i<=Length[rhs],i++,
		If[GFIiT[rhs[[i]] ]==gfidx,
			ret=True;
			Break[];
		];
	];
	ret
]
selfconsistent[gfidx_,rhs_Times]:=If[GFIiT[rhs]==gfidx,True,False]


(* MiT \:8fd4\:56de\:8f93\:5165\:9879\:4e2d\:7684\:4e58\:5b50\:ff0c\:5373\:8026\:5408\:5e38\:6570\:4e0e\:5b64\:7acb\:683c\:6797\:51fd\:6570\:4ee5\:53ca\:5176\:5b83\:81ea\:80fd *)
MiT[term_]:=Module[{i,ret=1,tp},
	For[i=1,i<=Length[term],i++,
		tp=type[term[[i]] ];
		If[tp==0 || tp==1 || tp==2 || tp==3,  (* if it is a passer-by or CC or iso-gf or SE *)
			ret*=term[[i]];
		];
	];
	ret
]

(* GFiT \:8fd4\:56de\:8f93\:5165\:9879\:4e2d\:7684\:683c\:6797\:51fd\:6570 *)
GFiT[term_OverBar]:=term
GFiT[term_Times]:=Module[{i,ret=1,tp},
	For[i=1,i<=Length[term],i++,
		tp=type[term[[i]] ];
		If[tp==4,
			ret*=term[[i]];
			Break[];  (* \:5982\:679c\:8fd8\:6709GF\:6211\:5c31\:628a\:952e\:76d8\:5403\:4e86 *)
		];
	];
	ret
]
(*GFiT[term_]:=Module[{},Print["Warning: unrecognizable term: ",term]; ]*)

type[expr_OverTilde]:=3 (* expr is a self-energy *)
type[expr_UnderBar]:=2 (* expr is a iso-gf *)
type[expr_OverBar]:=4 (* GF *)
type[expr_]:=Module[{ret=0},
	If[!FreeQ[CC,purepattern[expr]],   (* \:5982\:679c\:672c\:6765\:5e94\:8be5\:6709\:4e0b\:6807\:7684\:8026\:5408\:5e38\:6570\:ff0c\:4f46\:6ca1\:6709\:ff0c\:6b64\:65f6\:8fd9\:4e2a\:51fd\:6570\:8fd8\:662f\:4f1a\:5f53\:5b83\:662f\:8026\:5408\:5e38\:6570\:3002 *)
		ret=1; (* expr is a CC *)
	];
	ret (* if ret==0 then expr is a passer-by *)
]

(* CCinTerm \:51fd\:6570\:8fd4\:56de\:ffff\:771f\:ffff\:ff0c\:5982\:679c\:8f93\:5165\:9879\:4e2d\:5b58\:5728\:8026\:5408\:5e38\:6570 *)
CCinTerm[term_]:=Module[{tmp,ret=False,i,j},
	tmp=Cases[term,Except[_OverBar]];
	tmp=Cases[tmp,Except[_UnderBar]];
	tmp=Cases[tmp,Except[_OverTilde]];
	tmp=Level[tmp,-1];
	For[i=1,i<=Length[tmp],i++,
		For[j=1,j<=Length[ CC ] ,j++,
			If[MemberQ[CC[[j,1]],purepattern[ tmp[[i]] ]  ],
				ret=True;
				Break[];
			];
			If[MemberQ[CC[[j,2]],purepattern[ tmp[[i]] ]  ],
				ret=True;
				Break[];
			];
		];
		If[ret, Break[] ];
	];
	ret
]

(* GTIiT \:51fd\:6570\:628a\:8f93\:5165\:9879\:4e2d\:7684\:683c\:6797\:51fd\:6570\:7684\:5e8f\:53f7\:641e\:5230 *)
GFIiT[term_OverBar]:=Module[{j=0},
	j=Position[GFnames,purepattern[term] ];
	If[Length[j]>0,
		j=j[[1,1]];
	,
		Print["Error: what is this then??? ",term,"  ",term ];
		Abort[];
	];
	j
]
GFIiT[term_Times]:=Module[{pos,j=0},
	pos=Position[term,_OverBar];
	If[Length[pos]>1,
		Print["Error: Multiple GF's found in term ",term];
		Abort[];
	];
	If[Length[pos]==1,
		j=Position[GFnames,purepattern[ Extract[term,pos[[1]] ]   ]   ];
		If[Length[j]>0,
			j=j[[1,1]];
		,
			Print["Error: what is this?? ",term,"  ",pos[[1]]   ];
			Abort[];
		];
	];
	j   (* if pos returned no result, then j=0 *)
]
GFIiT[term_]:=0   (* meaning there is not a gf *)

(* { {ed,{t1d,t2d,....t1dstar...} }, {e[k],{tl[k],....} , ... } *)


(* grasp \:51fd\:6570\:628a\:80fd\:6536\:7684\:81ea\:80fd\:6536\:522e\:ff0c\:7136\:540e\:8fd4\:56de\:6536\:8fc7\:7684\:9879\:3002 *)
grasp[lhs_,recent_,term_Times]:=Module[{cc,params,poscore,dupterm=term,ret=term,eige,tmpmulti=1},
	(* \:5148\:627e\:662f\:5426\:6709\:914d\:5bf9\:7684\:8026\:5e38\:ff0c\:7136\:540e\:627e\:4e0e\:5b83\:4eec\:6709\:5171\:540c\:7684\:4e0b\:6807\:7684\:ff0c\:6216\:8005\:67e5\:5305\:542b\:8be5\:5b64\:7acb\:80fd\:7684\:ff0c\:5408\:8d77\:6765\:4f5c\:4e3a\:81ea\:80fd *)

	(* \:76ee\:524d\:7684\:7248\:672c\:53ea\:652f\:6301\:5355\:80fd\:7ea7\:7684\:3002\:591a\:80fd\:7ea7\:7684\:ff0c\:6211\:4f30\:8ba1\:53ef\:4ee5\:4ec5\:4ec5\:901a\:8fc7\:4e0b\:6807\:67e5\:51fa\:6765\:3002 *)

	(* \:5982\:679c\:6240\:627e\:5230\:7684\:4e0b\:6807 \:ff08\:6c42\:548c\:4e0b\:6807\:ff09\:5728\:7b49\:5f0f\:5de6\:8fb9\:4e5f\:51fa\:73b0\:8fc7\:ff0c\:5219\:4e0d\:80fd\:6536\:5b83\:4e3a\:81ea\:80fd\:ff0c\:56e0\:4e3a\:4e0d\:518d\:662f\:6c42\:548c\:7684\:4e86\:3002 *)

	For[cc=pairedCC[term],cc=!=0,cc=pairedCC[dupterm],
		(* there are paried CC, and therefore a self-energy *)
		(* \:9700\:8981\:641c\:7d22\:51fa\:4e0e\:8fd9\:4e24\:4e2a\:8026\:5408\:5e38\:6570\:5bf9\:5e94\:7684\:5176\:5b83\:5185\:5bb9 \:ff08\:5b64\:7acb\:683c\:6797\:51fd\:6570\:548c\:5176\:5b83\:5e94\:8be5\:5408\:5728\:4e00\:8d77\:7684\:81ea\:80fd\:ff09 *)

		(* \:7531\:4e8e\:5355\:80fd\:7ea7\:7684\:4e0d\:5e26\:4e0b\:6807\:ff0c\:6240\:4ee5\:5fc5\:987b\:6709\:5217\:8868\:52a0\:4ee5\:533a\:5206\:3002 *)
		If[Depth[cc[[1]]]==1, (* \:4e0d\:5e26\:4e0b\:6807 *)
			(* when the CC are non-subed, e.g., when dealing with single level problem, we must take extra care of the grasping. *)

			(* only one iso-gf is allowed...., if there **should** be any other SE's, they must be numbers so that we can treat them
			 as another group of passers-by *)
			eige=Select[SC,!FreeQ[#,cc[[1]] ] & ];
			If[Length[eige]==0,Print["Error: Single Level eigen energies must be reset by SetSingleCorr. "];Abort[]; ];
			eige=eige[[All,1]];
			poscore=Table[Select[IGFs,!FreeQ[#[[1]],purepattern[eige[[i]] ] ] & ] [[All,2]],  {i,Length[eige] } ] //Flatten;
			poscore=Select[recent,MemberQ[poscore,purepattern[#] ] & ];
			If[Length[poscore]>1,poscore=poscore[[1]]; Print["Warning: multiple possible cores found."];Abort[]; ];
			If[Length[poscore]==0,
				Print["Warning: Single level self energy found no core. lhs=",lhs," term=",dupterm," recent=",recent];
				Print["cc=",cc];
				ret=dupterm;
				ret=dupterm/cc[[1]]/cc[[2]]*SelfEnergySymbol[cc[[1]],1,cc[[2]],{} ];
			,
				ret=dupterm/poscore/cc[[1]]/cc[[2]]*SelfEnergySymbol[cc[[1]],poscore,cc[[2]],{} ];
			];
		,
			(* \:5e26\:4e0b\:6807 *)
			If[!(Depth[cc[[1]]]==2 && Depth[cc[[2]]]==2),
				Print["Error: subs ",cc[[1]] ];
				Abort[];
			];
			params=Intersection[Complement[Union[subs[cc[[1]]],subs[cc[[2]]]],subs[GFiT[dupterm] ]  ],   sumlist];
			(* i can just add one that the param should not be contained in G *)
			(*Print[params,"  ",cc];*)
			poscore=Select[dupterm/cc[[1]]/cc[[2]], paracont[params,#] & ];  (* \:6b64\:4e3e\:7b5b\:9009\:51fa\:8be5\:9879\:4e2d\:5305\:542b\:6240\:9700\:4e0b\:6807\:7684\:6240\:6709\:5143\:7d20 *)
(*				Print[poscore];*)

			If[(!FreeQ[poscore,_OverBar]) || poscore===1 ,
				(* poscore should not contain GF's or subs that is also contained in lhs *)
(*					Print[lhs, "  ren zai le."];*)
				ret=dupterm/cc[[1]]/cc[[2]];
				tmpmulti*=cc[[1]] cc[[2]];
			,
				ret=dupterm/poscore/cc[[1]]/cc[[2]]*SelfEnergySymbol[cc[[1]],poscore,cc[[2]] , params ];
			];
		];
		dupterm=ret;		
	];
	ret*tmpmulti
]

grasp[lhs_,recent_,term_Plus]:=Module[{}, Print["internal error: grasping a multiple of terms: ",term]; Abort[] ]
grasp[lhs_,recent_,term_]:=term  (* not know i need this one as well, sometimes we'll grasp a constant like "0"  *)

paracont[params_List,expr_]:=Module[{i,ret=False},
	For[i=1,i<=Length[params],i++,
		If[!FreeQ[expr,params[[i]] ],
			ret=True;
			Break[];
		];
	];
	ret
]

nonzero[l_List]:=If[l=!={},True,False]

pairedCC[termo_]:=Module[{term,i,j,rec={},pos,ret=0},  (* \:672c\:51fd\:6570\:627e\:8f93\:5165\:9879\:4e2d\:914d\:5bf9\:7684\:8026\:5408\:5e38\:6570 *)
	term=Level[termo,-1];
	For[i=1,i<=Length[term],i++,
		If[type[term[[i]]]==1, (* if it is a CC *)
			pos=Position[CC,purepattern[ term[[i]] ]  ];
			If[Length[pos]==0,
				Print["Error: coupling constant ",term[[i]]," not found."];
				Abort[];
			];
			AppendTo[rec,{term[[i]],pos[[1]]}];
		];
	];
	(* \:5982\:679c\:6709\:540c\:4e00\:4e2a\:7b2c\:4e00\:5143\:7d20\:ff0c\:7b2c\:4e8c\:5143\:7d20\:5206\:522b\:4e3a1\:548c2\:7684\:ff0c\:5c31\:7167\:4e86\:ff01 *)
	For[i=1,i<Length[rec],i++,  (* here it is < not <= *)
		For[j=i+1,j<=Length[rec],j++,
			If[rec[[i,2,1]]==rec[[j,2,1]] && ( rec[[i,2,2]]==1 && rec[[j,2,2]]==2 || rec[[i,2,2]]==2 && rec[[j,2,2]]==1 )  ,
				ret={rec[[i,1]],rec[[j,1]]};
				Break[];
			];
		];
		If[ret=!=0,
			Break[];
		];
	];
	ret
]		

(* ========================================================== \:5b59\:5e86\:5cf0\:89e3 ============================================================ *)

SetInterParam[a_List]:=Module[{},interparam=a]
SetInterParam[a__]:=SetInterParam[{a}]
zhangbian[coef_]:=Module[{ret=False,i},
	For[i=1,i<=Length[interparam],i++,
		If[!FreeQ[coef,interparam[[i]] ],
			ret=True;
			Break[];
		];
	];
	ret
]
GammaEnergySymbol[lhs_,numeritor_,denominator_]:=Module[{sl,sr,ret=0},
	If[MemberQ[GammaEnergy[[All,1;;2]],{numeritor,denominator} ],
		ret=GammaEnergy[[Position[GammaEnergy[[All,1;;2]],purepattern /@ {numeritor,denominator} ] [[1,1]],3]]
	];
(*un'comment this if not dealing with original 'devrim' setup	*)
	(*If[MemberQ[GammaEnergy[[All,1;;2]],purepattern /@ {-numeritor,denominator} ],
		ret=-GammaEnergy[[Position[GammaEnergy[[All,1;;2]],purepattern /@ {numeritor,denominator} ] [[1,1]],3]]
	];*)
	If[ret===0,
		If[denominator=!=1,
			sl=subs[lhs];
			sr=Union[subs[numeritor] ,subs[denominator] ];
			AppendTo[GammaEnergy,{numeritor,denominator,OverTilde[Unique["\[CapitalGamma]"] @@ 
				Sequence[Complement[sl,sr]]  ] }  ];
			If[nonzero[Complement[sr,sl] ],
				Print["internal error: extra subscripts in equation: ",lhs,"  ~~  ",numeritor/denominator];
				Abort[];
			];
			GammaEnergy[[-1,3]]
		,
			numeritor
		]
	,
		ret
	]
]

makereplist[l1_List,l2_List]:=Module[{},
	If[Length[l1]!=Length[l2],
		Print["Error: makereplist encountered lists with unequal length."];
		Abort[];
	];
	Table[l1[[i]]->l2[[i]],{i,Length[l1]}]
]

SelfEnergySymbol[c1_,core_,c2_,stealth_]:=Module[{i,ret=0,sub,subcc},
	(* this is a special version of treating U=0, extra vars: ss,isoincore *)

	(* if there's def for c1 core c2 typed self energy, return its symbol,
	 if not, create that SE and return the new symbol *)
	

	(* must add params *)



	For[i=1,i<=Length[SelfEnergy],i++,
		If[MatchQ[SelfEnergy[[i,1]],purepattern[c1 core c2] ],
			ret=SelfEnergy[[i,2]]/.makereplist[ subs[SelfEnergy[[i,1]] ] ,  subs[c1 core c2] ] ;  
	(* whether this SE has a sub or not does not matter here. if it has a stealh-sub, then it should word 
	 as well. *)
			Break[];
		];
	];
	If[ret==0,
(*		subcc=subs[c1 core c2];
		sub=Complement[subs[core],subcc ]; 
		*)
		sub=Complement[subs[c1 core c2], stealth];
		sub=sub~Join~Table[OverVector[stealth[[i]]],{i,Length[stealth]}];
		AppendTo[SelfEnergy,{c1 core c2,OverTilde[Unique["\[CapitalSigma]"] [ Sequence@@sub    ] ]  } ];
		ret=SelfEnergy[[-1,2]];
	];
	ret
]

gas[]:=jietu[]
jietu[] :=
    Module[{sym, symbol, out, left, coef, coef2, dest, dest2,
            currsol, unknown = {1}, done = {}, solgraph = {},
            idx, i, j},

        (* see if we are going to make "graph" an input *)

        sym  = Table[Unique["X"], {Length[gfs]}];
        left = Complement[unknown, done];
        Print["left: ", left];

        While[left =!= {},
            idx = left[[1]];
            Print["************************ ", idx];

            currsol = 0;

            For[out = 1, out <= Length[graph[[idx, 2]]], out++,
                coef = graph[[idx, 2, out, 2]];
                Print["coef: ", coef];

                dest = graph[[idx, 2, out, 1]];

                If[dest == 0,
                    currsol += coef;
                ,
                    Print["dest: ", dest];
                    symbol = sym[[dest]];
                    Print["symbol: ", symbol];

                    If[zhangbian[coef],
                        Print["zhangbian"];
                        currsol += coef*symbol;
                        Print[currsol];
                        unknown = Union[unknown, {dest}];
                        Print["unk: ", unknown];
                    ,
                        Print["pingbian"];
                        (* pingbian! need self energies *)

                        For[i = 1, i <= Length[graph[[dest, 2]]], i++,
                            dest2 = graph[[dest, 2, i, 1]];
                            Print["dest2: ", dest2];

                            If[dest2 == 0,
                                Print["this shouldn't happen...."];
                                Abort[];
                            ];

                            coef2 = graph[[dest, 2, i, 2]];
                            Print["coef2: ", coef2];

                            If[graph[[dest2, 1]] =!= 1,
                                Print[dest2, " is not trunc."];

                                currsol +=
                                    SelfEnergySymbol[coef, graph[[dest, 1]], coef2]*
                                    sym[[dest2]];
                                Print[currsol];

                                unknown = Union[unknown, {dest2}];
                                Print["unk: ", unknown];
                            ,
                                Print[dest2, " is trunc."];

                                For[j = 1, j <= Length[graph[[dest2, 2]]], j++,
                                    currsol +=
                                        SelfEnergySymbol[
                                            coef,
                                            graph[[dest, 1]],
                                            coef2*graph[[dest2, 2, j, 2]]
                                        ] * sym[[graph[[dest2, 2, j, 1]]]];
                                    Print[currsol];

                                    unknown =
                                        Union[unknown, {graph[[dest2, 2, j, 1]]}];
                                    Print["unk: ", unknown];
                                ];
                            ];
                        ];
                    ];
                ];
            ];

            (* if we meet a divide by 0 error here then we are screwed *)
            AppendTo[
                solgraph,
                sym[[idx]]/graph[[idx, 1]] == currsol
            ];

            done = Union[done, {idx}];
            left = Complement[unknown, done];
            Print["solgraph: ", solgraph];
        ];

        Print["SE: ", SelfEnergy];
    ]


kantu[]:=TableForm[Table[{i,graph[[i]]},{i,Length[graph]}]]

jiantu[] :=
    Module[{idx, pos, i, j, expr, gf, coef, outgo, val},
        (* by default start with 1st gf *)
        (* build the graph in the "graph-aided solution" by means of solgf data *)
        (* i doubt its necessity, but in this way one can think more easily *)

        graph = {};

        For[i = 1, i <= Length[gfs], i++,
            If[solgf[[i, 3]] =!= 0,
                
                pos = Position[solgf[[i, 3]], _UnderBar];
                If[Length[pos] > 0,
                    pos  = pos[[1]];
                    val  = Extract[solgf[[i, 3]], pos];
                    expr = ExpandAll[Simplify[solgf[[i, 3]]/val]];
                ,
                    val  = 1;
                    expr = solgf[[i, 3]];
                ];
                
                outgo = {};
                
                If[Head[expr] === Plus,
                    For[j = 1, j <= Length[expr], j++,
                        pos = Position[expr[[j]], _OverBar];
                        If[Length[pos] > 0,
                            pos = pos[[1]];
                            If[pos =!= {},
                                gf = Extract[expr[[j]], pos];
                            ,
                                gf = expr[[j]];
                            ];
                            idx  = Position[GFnames, purepattern[gf]];
                            coef = Simplify[expr[[j]]/gf];
                        ,
                            gf   = 1;
                            idx  = {{0}};
                            coef = expr[[j]];
                        ];
                        AppendTo[outgo, {idx[[1, 1]], coef}];
                    ];
                ,
                    pos = Position[expr, _OverBar];
                    If[Length[pos] > 0,
                        pos = pos[[1]];
                        gf  = Extract[expr, pos];
                        idx = Position[GFnames, purepattern[gf]];
                        coef = Simplify[expr/gf];
                    ,
                        gf   = 1;
                        idx  = {{0}};
                        coef = expr;
                    ];
                    AppendTo[outgo, {idx[[1, 1]], coef}];
                ];
                
                AppendTo[graph, {val, outgo}];
            ,
                (* if solgf[[i,3]]===0 *)
                AppendTo[graph, {0, {}}];
            ];
        ];  (* for i *)

        graph
    ]

	
del0[] :=
    Module[{i, tmp = {}},

        (* collect indices of GFs whose solution is identically 0 *)
        For[i = 1, i <= Length[gfs], i++,
            If[solgf[[i, 3]] == 0,
                AppendTo[tmp, i];
            ];
        ];

        (* eliminate those GFs (apply substitution diedaiTOsky) *)
        For[i = 1, i <= Length[gfs], i++,
            solgf[[i, 3]] = diedaiTOsky[solgf[[i, 3]], tmp];
        ];

        (* update eom to reflect modified solgf *)
        eom = solgf[[All, 3]];
    ]

cut0[expr_Plus]:=Sum[cut0[expr[[i]]],{i,Length[expr]}]
cut0[expr_Times]:=Product[cut0[expr[[i]]],{i,Length[expr]}]
cut0[expr_OverBar]:=If[diedaiTO[expr,0]==0,0,expr,expr]
cut0[expr_]:=expr


toa[gf_OverBar]:=OverBar[SuperPlus[gf[[1]]]]
toa[gf_]:=SuperPlus[gf]
tor[gf_OverBar]:=OverBar[SuperMinus[gf[[1]]]]
tor[gf_]:=SuperMinus[gf]
tol[gf_OverBar]:=OverBar[SubMinus[gf[[1]]]]
tol[gf_]:=SubMinus[gf]
tog[gf_OverBar]:=OverBar[SubPlus[gf[[1]]]]
tog[gf_]:=SubPlus[gf]

SetTrunc[a_List]:=Module[{}, trunclist=a; ]
SetTrunc[a__]:=SetTrunc[{a}]

SetExact[idx_Integer,max_Integer:6]:=Module[{i=1,orig,curr,rhs,tok=acGFnames[[idx]],zhibiao}, 
	Print[connectionlist];
	TableForm[Table[Flatten[{i,connectionlist[[i]]}],{i,Length[connectionlist]}]]
]

SetExact[expr_]:=Module[{pos},
	pos=Position[acGFnames,expr]//Flatten; (* the expr is assumed to be pattern *)
	If[Length[pos]==1,
		SetExact[pos[[1]]]
	,
		Print["destined GF not found"];
		expr
	]
]

ApplyExact[expr_List]:=Module[{}, (* here we assume output format of SetExact *)
	acGFsol[[expr[[1]]]]=expr[[2]];
]

(* ======================== ADVANCED ======================== *)

acAdvanced[expr_Plus, dt_Integer] :=
    Sum[acAdvanced[expr[[i]], dt], {i, Length[expr]}];

acAdvanced[expr_, dt_] :=
    Module[{c, pos, tmp, h},
        h   = Head[expr];
        tmp = List @@ expr;

        c   = Count[expr, _OverBar];
        pos = Position[expr, _OverBar, 1] // Flatten;

        Switch[c,
            1,
                tmp[[pos[[1]]]] = toa[tmp[[pos[[1]]]]],
            2,
                tmp[[pos[[1]]]] = toa[tmp[[pos[[1]]]]];
                tmp[[pos[[2]]]] = toa[tmp[[pos[[2]]]]]
        ];

        h @@ tmp
    ];


(* ======================== RETARDED ======================== *)

acRetarded[expr_Plus, dt_Integer] :=
    Sum[acRetarded[expr[[i]], dt], {i, Length[expr]}];

acRetarded[expr_, dt_] :=
    Module[{c, pos, tmp, h},
        h   = Head[expr];
        tmp = List @@ expr;

        c   = Count[expr, _OverBar];
        pos = Position[expr, _OverBar, 1] // Flatten;

        Switch[c,
            1,
                tmp[[pos[[1]]]] = tor[tmp[[pos[[1]]]]],
            2,
                tmp[[pos[[1]]]] = tor[tmp[[pos[[1]]]]];
                tmp[[pos[[2]]]] = tor[tmp[[pos[[2]]]]]
        ];

        h @@ tmp
    ];


(* ======================== LESSER ======================== *)

acLesser[expr_Plus, dt_Integer] :=
    Sum[acLesser[expr[[i]], dt], {i, Length[expr]}];

acLesser[expr_, dt_Integer] :=
    Module[{c, pos, tmp, t2 = 0, h},
        h   = Head[expr];
        tmp = List @@ expr;

        c   = Count[expr, _OverBar];
        pos = Position[expr, _OverBar, 1] // Flatten;

        Switch[c,
            (* One GF *)
            1,
                tmp[[pos[[1]]]] = tol[tmp[[pos[[1]]]]],

            (* Two GFs *)
            2,
                t2 = tmp;

                (* reordering rule based on tedian *)
                If[! tedian[tmp[[pos[[1]]]]] == dt,
                    (* swap positions *)
                    c         = pos[[1]];
                    pos[[1]]  = pos[[2]];
                    pos[[2]]  = c;
                ];

                (* first GF *)
                tmp[[pos[[1]]]] = tor[tmp[[pos[[1]]]]];
                t2[[pos[[1]]]]  = tol[t2[[pos[[1]]]]];

                (* second GF *)
                tmp[[pos[[2]]]] = tol[tmp[[pos[[2]]]]];
                t2[[pos[[2]]]]  = toa[t2[[pos[[2]]]]]
        ];

        h @@ tmp + h @@ t2
    ];


(* ======================== GREATER ======================== *)

acGreater[expr_Plus, dt_Integer] :=
    Sum[acGreater[expr[[i]], dt], {i, Length[expr]}];

acGreater[expr_, dt_Integer] :=
    Module[{c, pos, tmp, t2 = 0, h},
        h   = Head[expr];
        tmp = List @@ expr;

        c   = Count[expr, _OverBar];
        pos = Position[expr, _OverBar, 1] // Flatten;

        Switch[c,
            (* One GF *)
            1,
                tmp[[pos[[1]]]] = tog[tmp[[pos[[1]]]]],

            (* Two GFs *)
            2,
                t2 = tmp;

                If[! tedian[tmp[[pos[[1]]]]] == dt,
                    c         = pos[[1]];
                    pos[[1]]  = pos[[2]];
                    pos[[2]]  = c;
                ];

                (* first GF *)
                tmp[[pos[[1]]]] = tor[tmp[[pos[[1]]]]];
                t2[[pos[[1]]]]  = tog[t2[[pos[[1]]]]];

                (* second GF *)
                tmp[[pos[[2]]]] = tog[tmp[[pos[[2]]]]];
                t2[[pos[[2]]]]  = toa[t2[[pos[[2]]]]]
        ];

        h @@ tmp + h @@ t2
    ];


(* ======================== TEDIAN (type classifier) ======================== *)

tedian[expr_] :=
    Module[{ret = 3},  (* default: coefficient *)

        If[Head[expr] === OverBar,
            ret = 2            (* normal GF *)
        ];

        If[Head[expr] === OverBar && ! FreeQ[IGFs, Head[expr[[1]]]],
            ret = 1            (* forward/backward GF *)
        ];

        If[Head[expr] === OverBar && ! FreeQ[SelfEnergy, Head[expr[[1]]]],
            ret = 1            (* self-energy GF *)
        ];

        ret
    ];

(*SetDelta[a_]:=Module[{}, deltasymbol=a;]*)

GFxingshi[expr_Plus] :=
    Sum[GFxingshi[expr[[i]]], {i, Length[expr]}];

GFxingshi[expr_Times] :=
    Product[GFxingshi[expr[[i]]], {i, Length[expr]}];

GFxingshi[expr_NonCommutativeMultiply] :=
    Module[{ret = expr, pos},
        
        If[Length[expr] == 2,
            
            (* Case 1: creation on left, annihilation on right → reorder with minus *)
            If[creation[expr[[1]]] && annihilation[expr[[2]]],
                
                pos = Position[
                        gfs,
                        {purepattern[expr[[2]]], purepattern[expr[[1]]]}
                      ][[1, 1]];
                
                ret = -NonCommutativeMultiply[expr[[2]], expr[[1]]];
                (* minus sign is inevitable *)
                
                ret = -tol[GFnames[[pos]]] /. 
                        corr[gfs[[pos, 1]] ** gfs[[pos, 2]],
                             expr[[2]]    ** expr[[1]]];
            ];
            
            (* Case 2: annihilation on left, creation on right (normal ordering) *)
            If[creation[expr[[2]]] && annihilation[expr[[1]]],
                
                pos = Position[
                        gfs,
                        {purepattern[expr[[1]]], purepattern[expr[[2]]]}
                      ][[1, 1]];
                
                ret = tol[GFnames[[pos]]] /. 
                        corr[gfs[[pos, 1]] ** gfs[[pos, 2]],
                             expr[[1]]    ** expr[[2]]];
            ];
            
        ,
            (* More than two operators — not supported *)
            Print["da ge! 2 ge yi shang suan fu de wo gao bu ding a!!"];
        ];
        
        ret
    ]

GFxingshi[expr_]:=expr

sneak[]:={gfs,solgf,GFnames,acGFnames,acGFsol,trunclist,IGFs,SelfEnergy,GammaEnergy}

stealthsub[expr_Plus]:=Union[Flatten[Table[stealthsub[ expr[[i]] ],{i,Length[expr] } ] ] ]
stealthsub[expr_Times]:=Union[Flatten[Table[stealthsub[ expr[[i]] ],{i,Length[expr] } ] ] ]
stealthsub[expr_Power]:=stealthsub[expr[[1]] ]
stealthsub[expr_OverTilde]:=Cases[expr[[1]],_OverVector] //. OverVector[unigue_]->unigue
stealthsub[expr_]:={}  (* has to be self energy for now *)

subs[expr_NonCommutativeMultiply]:=Union[Flatten[Table[subs[expr[[i]]], {i,Length[expr]}]]] (* union could be put off *)
subs[expr_OverHat]:=subs[expr[[1]] ]  (*If[Depth[expr]==3,Level[expr,{-1}],{}]*)
subs[expr_OverBar]:=subs[expr[[1]] ]
subs[expr_UnderBar]:=subs[expr[[1]] ]
subs[expr_OverTilde]:=subs[expr[[1]] ]
subs[expr_Times]:=Flatten[Table[subs[expr[[i]]],{i,Length[expr]} ]]   (* it used to be union'ed *)
subs[expr_Plus]:=Union[Flatten[Table[subs[expr[[i]]],{i,Length[expr]}]]]
subs[expr_Power]:=subs[expr[[1]] ]
(* take off stealth-subs *)
subs[expr_]:=Module[{ret,i},
	ret=Select[ If[Depth[expr]>=2,Level[expr,{1}],{}]  , Head[#]=!=OverVector & ];
	For[i=1,i<=Length[ret],i++,
		If[Depth[ ret[[i]] ] > 1,
			ret[[i]]=Select[  Level[ret[[i]],{-1}]  ,  Head[#]=!=Integer & ];
		];
	];
	ret//Flatten
]
	
(* this union'ed version of subs may not be used in multiple dots, in which case orders must be taken. *)

(* solve. since the total number of GF's is limited, every single GF can have a closed-form solution. go
	from back to front, in this order we can guanrantee no "bubbles" in iteration *)

hebing[]:=Module[{},
	closedsol=Table[0,{Length[gfs]}]
]

exceed[ct_List,idx_Integer]:=Module[{i,ret=False},
	For[i=1,i<=Length[ct],i++,
		If[ct[[i]]>idx,
			ret=True;
			Break[]
		]
	];
	ret
]

repexceed[sol_,ct_List,idx_Integer]:=Module[{i,ret=sol},
	For[i=1,i<=Length[ct],i++,
		If[ct[[i]]>idx,
			ret=ret/.GFnames[[ ct[[i]] ]]->solgf[[ ct[[i]] , 3 ]]
			(* here sol should not contain index'ed GF's so it should work *)
		]
	];
	ret
]

jie[idx_Integer] :=
    Module[{sol, s2, ct},
        If[nonSubed[GFnames[[idx]]],
            
            sol = solgf[[idx, 3]];
            Print[idx, " ge shu: ", NRcontainedGF[sol]];
            
            ct = containedGF[sol];
            
            While[exceed[ct, idx],
                Print[idx, " die le :", ct, " aim: ", thre[ct, idx]];
                
                sol = diedaiTOsky[sol, thre[ct, idx]];
                
                If[idx > 8,
                    sol = Simplify[
                              sol,
                              TimeConstraint -> 10,
                              ComplexityFunction -> NRcontainedGF
                          ] //. selfenergyrep;
                ];
                
                Print[idx, " ge shu: ", NRcontainedGF[sol]];
                ct = containedGF[sol];
            ];
            
            Print[idx, " eq. ", ct];
            
            If[! FreeQ[sol, GFnames[[idx]]],
                sol = (Solve[GFnames[[idx]] == sol, GFnames[[idx]]] [[1, 1, 2]]);
            ];
            
            Print[idx, " solved"];
            
            If[idx > 6,
                sol = Simplify[
                          sol,
                          TimeConstraint -> 10,
                          ComplexityFunction -> NRcontainedGF
                      ] //. selfenergyrep;
            ];
            
            Print[idx, " simplified"];
            
            ct = containedGF[sol];
            Print["finally ", idx, " contains ", ct];
            
            If[MemberQ[ct, idx] || exceed[ct, idx],
                Print["Sorry: solution of GF #", idx,
                      " contained itself or later GF's. jie[", idx, "] failed."];
                Abort[]
            ,
                solgf[[idx, 3]] = sol
            ];
            
            Print[idx "zui zhong ge shu: ", NRcontainedGF[sol]];
            {idx, solgf[[idx, 3]]}
        ]
    ]

thre[ct_List,idx_Integer]:=Select[ct,#>idx &]

fhdaijie[idx_Integer] :=
    Module[{sol, ct, cta},

        sol = solgf[[idx, 3]];
        ct  = subbed[containedGF[sol]];

        Print[idx, "   ", ct];

        (* Iteratively eliminate higher-index GFs *)
        While[Length[thre[ct, idx]] > 0,

            sol = diedaiTOsky[sol, thre[ct, idx]];  
            sol = Simplify[
                    sol,
                    ComplexityFunction -> NRcontainedGF,
                    TimeConstraint -> 10
                  ];

            cta = containedGF[sol];
            ct  = subbed[cta];

            Print[idx, "  die le  ", cta,
                  " ge shu: ", NRcontainedGF[sol],
                  " zhong shu: ", Length[cta]];
        ];

        Print[idx, " eq. ", containedGF[sol]];

        (* Solve implicit GF if present on both sides *)
        If[! FreeQ[sol, GFnames[[idx]]],
            sol = Solve[GFnames[[idx]] == sol, GFnames[[idx]]] [[1, 1, 2]];
        ];

        Print[idx, " solved"];

        (* Final simplification *)
        sol = Simplify[
                sol,
                TimeConstraint -> 10,
                ComplexityFunction -> NRcontainedGF
              ];

        Print[idx, "  Simplified"];
        Print["finally ", idx, " contains ", containedGF[sol]];

        (* Check for self-dependence *)
        If[MemberQ[containedGF[sol], idx],
            Print["Sorry: solution of GF #", idx,
                  " contained itself. fhdaijie[", idx, "] failed."];
            Abort[],
            solgf[[idx, 3]] = sol
        ];

        Print["ge shu: ", NRcontainedGF[sol]];

        {idx, solgf[[idx, 3]]}
    ]


fen[] :=
    Module[{k, i, s},

        category =
            Table[{}, {it, Length[trunclist]}, {2 + trunclist[[it, 2]]}];

        Print[category];

        For[k = 1, k <= Min[cap, Length[gfs]], k++,
            For[i = 1, i <= Length[trunclist], i++,
                s = Sum[
                        Count[
                            gfs[[k, 1]]**gfs[[k, 2]],
                            trunclist[[i, 1, j]],
                            Infinity
                        ],
                        {j, Length[trunclist[[i, 1]]]}
                    ];

                If[s > 0,
                    category[[i, s]] =
                        Union[category[[i, s]], {k}];
                ];
            ];
        ];

        Print[category];

        i = Length[category];

        For[s = Length[category[[i]]] - 1, s > 0, s--,
            category[[i, s]] =
                Union[category[[i, s]], category[[i, s + 1]]];
        ];

        For[i = Length[category] - 1, i > 0, i--,
            category[[i, -1]] =
                Union[category[[i, -1]], category[[i + 1, 1]]];

            For[s = Length[category[[i]]] - 1, s > 0, s--,
                category[[i, s]] =
                    Union[category[[i, s]], category[[i, s + 1]]];
            ];
        ];

        Print[category];
    ]


yaoqiu0[ct_List,cat_Integer,geshu_Integer,idx_Integer]:=Intersection[ct,category[[cat,geshu]] ]
yaoqiuq[ct_List,cat_Integer,geshu_Integer,idx_Integer]:=Intersection[ct,category[[cat,geshu]] ]
yaoqiuh[ct_List,cat_Integer,geshu_Integer,idx_Integer]:=Select[Intersection[ct,category[[cat,geshu]] ],#>idx&]

FenJie[verbo_:0]:=Module[{cat,geshu,iter,uu,tt},
	fen[];
	tt=TimeUsed[];
	For[cat=Length[category],cat>0,cat--,
		For[geshu=Length[category[[cat]] ],geshu>0,geshu--,
			If[Length[category[[cat,geshu]]]>0,
				Print["cat: ",cat,"  geshu: ",geshu];
				uu=TimeUsed[];
				For[iter=Length[gfs],iter>0,iter--,
					If[iter!=14,
						fenjie[verbo,yaoqiuh,iter,cat,geshu]
					,
						fenjie[1,yaoqiuh,iter,cat,geshu]
					];
				];
				For[iter=Length[gfs],iter>0,iter--,
						If[fenjie[verbo,yaoqiu0,iter,cat,geshu]==False,
							Print["Error: fenjie[",iter,"] failed."];
						];
				];
				Print["Pass cat: ",cat,"  geshu: ",geshu," done in ",TimeUsed[]-uu," seconds."];
			];
		];
	];
	Print["everything done in ",TimeUsed[]-tt," seconds."];
]

FenDie[verbo_:0]:=Module[{cat,geshu,iter,uu,tt},
	fen[];
	tt=TimeUsed[];
	For[cat=Length[category],cat>0,cat--,
		For[geshu=Length[category[[cat]] ],geshu>0,geshu--,
			If[Length[category[[cat,geshu]]]>0,
				Print["cat: ",cat,"  geshu: ",geshu];
				uu=TimeUsed[];
				For[iter=Length[gfs],iter>0,iter--,
					fendie[0,yaoqiuh,iter,cat,geshu]
				];
				Print["Pass cat: ",cat,"  geshu: ",geshu," done in ",TimeUsed[]-uu," seconds."];
			];
		];
	];
	Print["everything done in ",TimeUsed[]-tt," seconds."];
]
				

fendie[verbo_:0,yaoqiu_,idx_Integer,cat_Integer,geshu_Integer]:=Module[{sol,ct,cta,ret=True,s2,nr},
	Print[" num: ",idx," cat: ",cat," geshu: ",geshu];
	sol=solgf[[idx,3]];
	If[sol=!=0,
		If[verbo>0,Print["getting GF index ..."];];
		ct=containedGF[sol];
		nr=NRcontainedGF[sol];
		cta=yaoqiu[ct,cat,geshu,idx];
		If[verbo>0,Print["indexing done."];];
		If[verbo>0,Print["initial: ",Length[ct]," GF's and ",Length[cta]," GF's to be iterated. ",cta," ge shu :",nr];];
		While[Length[cta]>0,
			If[verbo>0,Print[idx," diedai-ing ...",ct];];
			sol=grab3[ExpandAll[diedaiTOsky[sol,cta]]]//.selfenergyrep;
			nr=NRcontainedGF[sol];
			If[verbo>0,Print["diedai done. ge shu: ",nr,"\n simplifying..."];];
			sol=Simplify[sol,ComplexityFunction->NRcontainedGF,TimeConstraint->10]//.selfenergyrep;
			If[verbo>0,Print["simplify done.\n getting index..."];];
			ct=containedGF[sol];
			cta=yaoqiu[ct,cat,geshu,idx];
			If[verbo>0,Print["iteration: ",Length[ct]," GF's and ",Length[cta]," GF's to be iterated. ",cta];];
		];
		If[verbo>0,Print[idx," eq. ",ct ];];
		ct=containedGF[sol];
		If[verbo>0,Print["finally ", idx," contains ",ct," ge shu: ",NRcontainedGF[s2]  ];];
		solgf[[idx,3]]=sol;  (* this is true, it only contains itself, eliminate it next time. *)
		If[verbo>1,
			Print[sol]
		];
	];
]

fenjie[verbo_: 0, yaoqiu_, idx_Integer, cat_Integer, geshu_Integer] :=
    Module[{sol, ct, cta, ret = True, s2, nr},

        Print[" num: ", idx, " cat: ", cat, " geshu: ", geshu];

        sol = solgf[[idx, 3]];

        If[verbo > 0, Print["getting GF index ..."];];

        ct  = containedGF[sol];
        nr  = NRcontainedGF[sol];
        cta = yaoqiu[ct, cat, geshu, idx];

        If[verbo > 0, Print["indexing done."];];
        If[verbo > 0,
            Print["initial: ", Length[ct], " GF's and ",
                  Length[cta], " GF's to be iterated. ",
                  cta, " ge shu :", nr];
        ];

        While[Length[cta] > 0,

            If[verbo > 0, Print[idx, " diedai-ing ...", ct];];

            sol = diedaiTOsky[sol, cta] //. selfenergyrep;
            nr  = NRcontainedGF[sol];

            If[verbo > 0,
                Print["diedai done. ge shu: ", nr, "\n simplifying..."];
            ];

            sol = Simplify[
                    sol,
                    ComplexityFunction -> NRcontainedGF,
                    TimeConstraint     -> 10
                  ] //. selfenergyrep;

            If[verbo > 0, Print["simplify done.\n getting index..."];];

            ct  = containedGF[sol];
            cta = yaoqiu[ct, cat, geshu, idx];

            If[verbo > 0,
                Print["iteration: ", Length[ct], " GF's and ",
                      Length[cta], " GF's to be iterated. ",
                      cta];
            ];
        ];

        If[verbo > 0, Print[idx, " eq. ", ct];];

        If[! FreeQ[sol, GFnames[[idx]]],
            s2 = (Solve[GFnames[[idx]] == sol, GFnames[[idx]]] [[1, 1, 2]]) //. selfenergyrep;
            If[verbo > 0, Print[idx, " solved."];];

            s2 = Simplify[
                    s2,
                    TimeConstraint     -> 10,
                    ComplexityFunction -> NRcontainedGF
                 ] //. selfenergyrep;

            If[verbo > 0, Print[idx, " simplified."];];
        ,
            s2 = sol;
            If[verbo > 0, Print[idx, " solved & simplified."];];
        ];

        ct = containedGF[s2];

        If[verbo > 0,
            Print["finally ", idx, " contains ",
                  ct, " ge shu: ", NRcontainedGF[s2]];
        ];

        If[MemberQ[ct, idx],
            Print["Sorry: solution of GF #", idx,
                  " contained itself. fenjie[",
                  idx, ",", cat, ",", geshu, "] failed."];

            (* this is true, it only contains itself, eliminate it next time. *)
            solgf[[idx, 3]] = sol;
            ret = False;
        ,
            solgf[[idx, 3]] = s2;
        ];

        If[verbo > 1,
            Print[s2];
        ];

        ret
    ]


sljie[idx_Integer] :=
    Module[{sol, ct, cta},

        sol = solgf[[idx, 3]];
        ct  = subbed[containedGF[sol]];

        Print[idx, "   ", ct];

        While[Length[ct] > 0,

            sol = grab3[ExpandAll[diedaiTOsky[sol, ct]]] //. selfenergyrep;

            sol = Simplify[
                    sol,
                    ComplexityFunction -> NRcontainedGF,
                    TimeConstraint     -> 10
                  ];

            cta = containedGF[sol];
            ct  = subbed[cta];

            Print[idx, "  die le  ", cta,
                  " ge shu: ", NRcontainedGF[sol],
                  " zhong shu: ", Length[cta]];
        ];

        Print[idx, " eq. ", containedGF[sol]];

        If[! FreeQ[sol, GFnames[[idx]]],
            sol = Solve[GFnames[[idx]] == sol, GFnames[[idx]]] [[1, 1, 2]];
        ];

        Print[idx, " solved"];

        sol = Simplify[
                sol,
                TimeConstraint     -> 10,
                ComplexityFunction -> NRcontainedGF
              ];

        ct = containedGF[sol];

        Print["finally ", idx, " contains ", ct];

        If[MemberQ[ct, idx],
            Print["Sorry: solution of GF #", idx,
                  " contained itself. sljie[", idx, "] failed."];
            Abort[]
        ,
            solgf[[idx, 3]] = sol
        ];

        Print["ge shu: ", NRcontainedGF[sol]];

        {idx, solgf[[idx, 3]]}
    ]


danjie[lv_Integer : 3, res_ : False] :=
    Module[{i, uu, tt},
        (* lv: 3 -> fhdaijie + sljie + jie
                2 -> sljie + jie
                1 -> jie only *)

        uu = TimeUsed[];
        tt = uu;

        (* Pass 1: fhdaijie on all GFs *)
        If[lv > 2,
            Print["Pass 1:"];
            For[i = Length[gfs], i > 0, i--,
                If[res === True,
                    Print[fhdaijie[i]],
                    fhdaijie[i]
                ]
            ];
            Print["Pass 1 done in ", TimeUsed[] - uu, " seconds."];
        ];

        uu = TimeUsed[];

        (* Pass 2: sljie on all GFs *)
        If[lv > 1,
            Print["Pass 2:"];
            For[i = Length[gfs], i > 0, i--,
                If[res === True,
                    Print[sljie[i]],
                    sljie[i]
                ]
            ];
            Print["Pass 2 done in ", TimeUsed[] - uu, " seconds."];
        ];

        uu = TimeUsed[];

        (* Final Pass: jie on all GFs *)
        Print["Final Pass...."];
        For[i = Length[gfs], i > 0, i--,
            If[res === True,
                Print[jie[i]],
                jie[i]
            ];
        ];
        Print["Pass 3 done in ", TimeUsed[] - uu, " seconds."];
        Print["everything done in ", TimeUsed[] - tt, " seconds."];
    ]
	

(*

 codes for diedaiTOs has been replaced by diedaiTOsky, which is a lot faster 

diedaiTOs[expr_Plus,curr_List]:=Sum[diedaiTOs[expr[[i]],curr],{i,Length[expr]}] 
diedaiTOs[expr_Times,curr_List]:=(Product[diedaiTOs[expr[[i]],curr],{i,Length[expr]}] )
diedaiTOs[expr_OverBar,curr_List]:=Module[{pos},
	pos=Flatten[Position[GFnames,purepattern[expr],1]];
	If[Length[pos]!=0,
		If[Length[pos]>1,
			Print["Error: Multiple of Green's Function ",expr," found in list."];
			Abort[];
		];
		pos=pos[[1]];
		If[MemberQ[curr,pos],
			solgf[[pos,3]]/.GFTOsubsub[GFnames[[pos]],expr]
		,
			expr
		]
	,
		expr
	]
]
diedaiTOs[expr_,curr_List]:=expr   *)

diedaiTOsky[expr_OverBar, curr_List] :=
    Module[{pos, i, ret = expr, tok, idx},

        tok = expr;

        Print["tick"];

        idx = Flatten[Position[GFnames, purepattern[tok]]];
        Print[idx];

        If[Length[idx] != 1,
            Print["Error: Multiple or no GF's found for ", tok];
            Abort[];
        ];

        idx = idx[[1]];
        Print[idx];

        If[MemberQ[curr, idx],
            ret = solgf[[idx, 3]] /. GFTOsubsub[GFnames[[idx]], tok];
        ];

        ret
    ]


diedaiTOsky[expr_,curr_List]:=Module[{pos,i,ret=expr,tok,idx},
	pos=Position[expr,_OverBar];
	For[i=1,i<=Length[pos],i++,
		tok=Extract[expr,pos[[i]]];
		idx=Flatten[Position[GFnames,purepattern[tok]]];
		If[Length[idx]!=1,
			Print["Error: Multiple or no GF's found for ",tok];
			Abort[];
		];
		idx=idx[[1]];

		If[MemberQ[curr,idx],
			Part[ret,pos[[i]]/.List->Sequence]=solgf[[idx,3]]/.GFTOsubsub[GFnames[[idx]],tok];
		];
	];
	ret
]

subbed[cgf_List]:=Module[{i,ret={}},
	For[i=1,i<=Length[cgf],i++,
		If[!nonSubed[GFnames[[ cgf[[i]] ]]],
			AppendTo[ret,cgf[[i]] ]
		]
	];
	ret
]
NRcontainedGF[expr_]:=Count[expr,_OverBar,Infinity]
(*
NRcontainedGF[expr_]:=Module[{pos,i,ret=0,pos2},
	pos=Position[expr,_OverBar];
	For[i=1,i<=Length[pos],i++,
		tmp=Extract[expr,pos[[i]] ];
		pos2=Flatten[ Position[GFnames,purepattern[tmp],1 ]  ];
		ret+=Length[pos2];
	];
	ret
]
*)
containedGF[expr_]:=Module[{pos,i,ret={},pos2},
	pos=Position[expr,_OverBar];
	For[i=1,i<=Length[pos],i++,
		tmp=Extract[expr,pos[[i]] ];
		pos2=Flatten[ Position[GFnames,purepattern[tmp],1 ]  ];
		If[Length[pos2]>0,
			AppendTo[ret,pos2[[1]]];
		]
	];
	Union[ret]
]
nonSubed[var_OverBar]:=If[Length[var[[1]] ]==0,True,False,False]

		
(* ==== diedaiTO is for time ordered GF, more "raw" than AC'ed GF's *)
diedaiTO[expr_Plus, curr_Integer] :=
    Sum[
        diedaiTO[expr[[i]], curr],
        {i, Length[expr]}
    ] 
    (* /. selfenergyrep *)   (* ← kept as your original comment *)

diedaiTO[expr_Times, curr_Integer] :=
    Expand[
        Product[
            diedaiTO[expr[[i]], curr],
            {i, Length[expr]}
        ]
    ]

diedaiTO[expr_OverBar, curr_Integer] :=
    Module[{pos},

        (* this is a GF *)
        pos = Flatten[
            Position[GFnames, purepattern[expr], 1]
        ];

        If[Length[pos] != 0,

            (* found at least one GF match *)
            If[Length[pos] > 1,
                Print[
                    "Error: Multiple of Green's Function ", expr,
                    " found in list."
                ];
                Abort[];
            ];

            pos = pos[[1]];  (* take the unique match index *)

            If[curr < pos,
                (* substitute in solved GF expression *)
                solgf[[pos, 3]] /. GFTOsubsub[GFnames[[pos]], expr],
                (* else leave as-is *)
                expr
            ],

            (* no match in GFnames → return expr unchanged *)
            expr
        ]
    ]

diedaiTO[expr_, curr_Integer] := expr   (* no change for non-gf exp's *)


diedai[expr_Plus]:=Sum[diedai[expr[[i]]],{i,Length[expr]}]
diedai[expr_OverBar]:=Module[{pos},
	pos=Position[acGFnames,expr/.
		Table[Level[expr,{3}][[i]]->Blank[],{i,Length[Level[expr,{3}]]}]] ;  (* position in gf list *)
	If[Length[pos]==1,
		pos=pos[[1,1]];
		If[FreeQ[final,pos],
			ExpandAll[(acGFsol[[pos]])/.GFsubsub[acGFnames[[pos]],expr]]/.selfenergyrep
		,
			expr
		]
	,
		expr
	]
]

diedai[expr_] := expr

diedai[expr_Times] :=
    Module[{pl, i, tmp, h, gf, subl, pos},

        h   = Head[expr];
        tmp = List @@ expr;

        (* positions of Green's functions (OverBar) in the product *)
        pl = Position[expr, _OverBar, 1] // Flatten;

        For[i = 1, i <= Length[pl], i++,

            gf   = tmp[[pl[[i]]]];
            subl = Level[gf, {3}];

            (* match GF with acGFnames by replacing subs with blanks *)
            pos = Position[
                    acGFnames,
                    gf /. Table[subl[[i]] -> Blank[], {i, Length[subl]}]
                  ] // Flatten;

            If[Length[pos] == 0, Continue[]];

            pos = pos[[1]];

            (* substitute solution for this ac GF *)
            tmp[[pl[[i]]]] =
                acGFsol[[pos]] /. GFsubsub[acGFnames[[pos]], tmp[[pl[[i]]]]];
        ];

        Grab[
            ExpandAll[h @@ tmp] /. selfenergyrep
        ]
    ]


GFsubsub[a_OverBar, b_OverBar] :=
    Table[a[[1, 1, i]] -> b[[1, 1, i]], {i, Length[a[[1, 1]]]}];

GFTOsubsub[a_OverBar, b_OverBar] :=
    Table[a[[1, i]] -> b[[1, i]], {i, Length[a[[1]]]}];  (* all GF's have depth 2 *)

ISOsubsub[a_UnderBar, b_UnderBar] :=
    Table[a[[1, i]] -> b[[1, i]], {i, Length[a[[1]]]}];  (* all GF's have depth 2 *)


ResetGFlist[] :=
    Module[{},
        gfs     = {};
        solgf   = {};
        GFnames = {};
    ];


ResDisp[] :=
    Module[{},
        Print["************* Equation(s) of motion: *************"];
        TableForm[
            Table[
                {i, ":  <<", Sequence @@ gfs[[i]], ">> =", solgf[[i, 3]]},
                {i, Length[gfs]}
            ]
        ] // Print;
        Print[];

        Print["************* Isolated Green's Function(s): *************"];
        TableForm[
            Table[
                {IGFs[[i, 2]], " \[Congruent] ", IGFs[[i, 1]]},
                {i, Length[IGFs]}
            ]
        ] // Print;

        If[SelfEnergy =!= {},
            Print["************ Self-Energy(ies): ************ "];
            TableForm[
                Table[
                    {SelfEnergy[[i, 2]], " \[Congruent] ", SelfEnergy[[i, 1]]},
                    {i, Length[SelfEnergy]}
                ]
            ] // Print;
        ];

        If[GammaEnergy =!= {},
            TableForm[
                Table[
                    {GammaEnergy[[i, 2]], " \[Congruent] ", GammaEnergy[[i, 1]]},
                    {i, Length[GammaEnergy]}
                ]
            ] /. GlobalSummationScript -> Unique["s"] // Print;
        ];
    ]


SetCoupling[a_List]:=Module[{}, CC=a;plainCC=Flatten[CC]; 
	Print["Grouped coupling constants:"];
	Print[ TableForm[CC] ];
	Print[]
]
SetCoupling[a__]:=SetCoupling[{a}]
prep[]:=Module[{},Print[selfenergyrep];]
(*SetSelfEnergy[a_List]:=Module[{i,l=Length[a],tmp}, selfenergyrep = a; SelfEnergy=a[[All,2]]; 
]
SetSelfEnergy[a__]:=SetSelfEnergy[{a}]
*)
SetRules[a_List] := Module[{}, rulelist = a; 
	Print["(Anti-)Commutation relation(s): "];
	Print[ 
		TableForm[  
			Table[ 
				If[Head[a[[i,3]] ]===RuleDelayed,
					{i,":  {",a[[i,3,1,1]],",",a[[i,3,1,2]],"} =",a[[i,3,2]]}
				,
					{i,":  {",a[[i,1]],",",a[[i,2]],"} =",a[[i,3]] }
				]
			,{i,Length[a] }
			]
		]
	];
	Print[]
]

SetRules[a__] := SetRules[{a}]
SetPreserve[a_List] := Module[{}, preservelist = a; 
	Print["Operators to preserve: ",a];
	Print[]
]

SetPreserve[a__] := SetPreserve[{a}]
SetETPreserve[a_List]:=Module[{},ETP=a;]
ETjudge[dt_Plus]:=Sum[ETjudge[dt[[i]]],{i,Length[dt]}]
ETjudge[dt_Times]:=Product[ETjudge[dt[[i]]],{i,Length[dt]}]
ETjudge[dt_OverHat]:=dt
ETjudge[dt_NonCommutativeMultiply]:=Module[{i,pos,ret=dt},
	pos=Position[ETP,purepattern[dt[[1]]]];
	If[Length[pos]>1,
		Print["Warning: multiple slots found for operator ",dt[[1]]  ];
	];
	If[Length[pos]>0,
		pos=Flatten[pos][[1]];
		For[i=2,i<=Length[dt],i++,
			If[!MemberQ[ETP[[pos]],purepattern[dt[[i]] ] ],
				ret=0;
				Break[];
			];
		];
	,
		ret=0;
	];
	ret
	(* dt  (* keep everything *) *)
]

ETjudge[dt_] := dt


SetSumSub[a_List] :=
    Module[{},
        sumlist = a;
        Print["List of summation subscript: ", a];
        Print[];
    ]

SetSumSub[a__] := SetSumSub[{a}]


sneaksumlist[] := sumlist


SetIGF[a_List] :=
    Module[{},
        IGFs     = a;
        oriNRIGF = Length[a];
    ]

SetIGF[a__] := SetIGF[{a}]


MakeSE[] :=
    Module[{i, j, k},
        For[i = 1, i <= Length[IGFs], i++,
            For[j = 1, j < oriNRIGF, j++,   (* exclude the last one, which conforms "SetPreserve" *)
                If[! FreeQ[IGFs[[i, 1]], IGFs[[j, 1]]],
                    If[Depth[IGFs[[i, 2]]] == 2,
                        AppendTo[
                            selfenergyrep,
                            UnderBar[
                                (IGFs[[i, 2]] /. IGFs[[i, 2, 1]] -> IGFs[[j, 2, 1]])
                            ] *
                            Product[
                                IGFs[[j, 3, m]],
                                {m, Length[IGFs[[j, 3]]]}
                            ] -> Unique["\[CapitalSigma]"]
                        ];
                    ,
                        AppendTo[
                            selfenergyrep,
                            UnderBar[IGFs[[i, 2]]] *
                            Product[
                                IGFs[[j, 3, m]],
                                {m, Length[IGFs[[j, 3]]]}
                            ] -> Unique["\[CapitalSigma]"]
                        ];
                    ];
                    Break[];
                ];
            ];
        ];
        Print[selfenergyrep];
    ]


annihilation[op_OverHat] :=
    Module[{i, ret = False},
        For[i = 1, i <= Length[rulelist], i++,
            If[MatchQ[op[[1]], rulelist[[i, 1]]] == True,
                ret = True;
            ];
        ];
        ret
    ]


creation[op_OverHat] :=
    Module[{i, ret = False},
        For[i = 1, i <= Length[rulelist], i++,
            If[MatchQ[op[[1]], rulelist[[i, 2]]] == True,
                ret = True;
            ];
        ];
        ret
    ]


ZhaoGF[expr_] :=
    Module[{},
        ResetGFlist[];
        zhaogf[expr];
        Print["Target Green's function set as: ", gfs[[1]]];
    ]

TargetGF[expr_] := ZhaoGF[expr]


zhaogf[expr_Plus] :=
    Sum[zhaogf[expr[[i]]], {i, Length[expr]}]

zhaogf[expr_Times] :=
    Sum[zhaogf[expr[[i]]], {i, Length[expr]}]

zhaogf[expr_NonCommutativeMultiply] :=
    Module[{k = 0},
        If[Length[expr] == 2 && annihilation[expr[[1]]] && creation[expr[[2]]],
            AppendTo[gfs, {uniquesub[expr[[1]]], uniquesub[expr[[2]]]}];
            AppendTo[solgf, {0, 0, 0}];
            AppendTo[
                GFnames,
                OverBar[
                    Unique["GF"] @@ subs[gfs[[-1, 1]] ** gfs[[-1, 2]]]
                ]
            ];
            k = 1;
        ];

        If[Length[expr] == 2 && annihilation[expr[[2]]] && creation[expr[[1]]],
            AppendTo[gfs, {uniquesub[expr[[2]]], uniquesub[expr[[1]]]}];
            AppendTo[solgf, {0, 0, 0}];
            AppendTo[
                GFnames,
                OverBar[
                    Unique["GF"] @@ subs[gfs[[-1, 1]] ** gfs[[-1, 2]]]
                ]
            ];
            k = 1;
        ];
        k
    ]

zhaogf[expr_] := 0


preserveQ[op_OverHat] :=
    Module[{i, ret = False},
        For[i = 1, i <= Length[preservelist], i++,
            If[MatchQ[op, preservelist[[i]]],
                ret = True;
            ];
        ];
        ret
    ]

preserveQ[e_] := False


FengZhuang[expr_] :=
    Module[{ret},
        If[expr === 0,
            Print["Error: fengzhuang called with zero argument."];
            Abort[];
        ];
        ret = fenzhuang[expr];
        If[Head[ret[[1]]] =!= List,
            ret = {ret};
        ];
        ret
    ]


fenzhuang[expr_Plus] :=
    Module[{c = {}, i, j},
        For[i = 1, i <= Length[expr], i++,
            AppendTo[c, fenzhuang[expr[[i]]]];
        ];
        c
    ]


fenzhuang[expr_Times] :=
    Module[{kk = expr, re = {}},
        If[FreeQ[expr, NonCommutativeMultiply] == False,
            (* 里面有算符积 *)
            For[i = 1, i <= Length[expr], i++,
                If[expr[[i, 0]] == NonCommutativeMultiply,
                    AppendTo[re, expr[[i]]];
                    kk[[i]] = 1;
                    AppendTo[re, kk];
                ];
            ];
        ,
            (* 里面没有算符积，但有算符 *)
            If[FreeQ[expr, OverHat] == False,
                For[i = 1, i <= Length[expr], i++,
                    If[expr[[i, 0]] == OverHat,
                        AppendTo[re, expr[[i]]];
                        kk[[i]] = 1;
                        AppendTo[re, kk];
                    ];
                ];
            ,
                (* 什么都没有 *)
                Print["shenmedou mei"];
            ];
        ];
        re
    ]


(* ===================== fenzhuang extensions ===================== *)

fenzhuang[expr_NonCommutativeMultiply] := {expr, 1}
fenzhuang[expr_OverHat]               := {expr, 1}


(* ===================== AC: build component GFs ===================== *)

AC[gi_] :=
    Module[{},
        acGFnames =
            Table[
                {
                    toa[GFnames[[i]]],
                    tor[GFnames[[i]]],
                    tol[GFnames[[i]]],
                    tog[GFnames[[i]]]
                },
                {i, gi}
            ] // Flatten;

        acGFsol =
            Table[
                {
                    acAdvanced[solgf[[i, 3]], solgf[[i, 1]]],
                    acRetarded[solgf[[i, 3]], solgf[[i, 1]]],
                    acLesser[solgf[[i, 3]],   solgf[[i, 1]]],
                    acGreater[solgf[[i, 3]],  solgf[[i, 1]]]
                },
                {i, gi}
            ] // Flatten;
    ]


(* ===================== DeriveGF: main EOM driver ===================== *)

DeriveGF[Hamiltonian_] :=
    Module[{tim, kk, GFlistIndex = 1, rhs, dt, deltatimes, trid},

        Print["Deriving..."];
        tim = TimeUsed[];

        While[GFlistIndex <= Length[gfs],

            (* decide which operator (1: creation side, 2: annihilation side) *)
            If[preserveQ[gfs[[GFlistIndex, 2]]],
                dt = 1,
                dt = 2
            ];

            (* fermionic rule: two identical operators → zero *)
            If[twoidentical[gfs[[GFlistIndex, dt]]],
                solgf[[GFlistIndex, 1]] = dt;
                solgf[[GFlistIndex, 2]] = 0;
                solgf[[GFlistIndex, 3]] = 0;
                AppendTo[connectionlist, {}];  (* no connections if identically zero *)
                GFlistIndex++;
                Continue[];
            ];

            trid = yao[gfs[[GFlistIndex, dt]]];  (* truncation id / status *)

            If[trid == 0,
                (* full commutator-based equation of motion *)

                If[dt == 1,
                    rhs =
                        FengZhuang[
                            Grab[
                                ExpandAll[
                                    com[gfs[[GFlistIndex, 1]], Hamiltonian]
                                ] //. {
                                    (a_) ** (b_ + c_) :> a ** b + a ** c,
                                    (a_ + b_) ** c_   :> a ** c + b ** c,
                                    (a_ b_) ** c_     :> a ** b ** c,
                                    a_ ** (b_ c_)     :> a ** b ** c
                                }
                            ]
                        ]
                ,
                    rhs =
                        FengZhuang[
                            Grab[
                                -ExpandAll[
                                    com[gfs[[GFlistIndex, 2]], Hamiltonian]
                                ] //. {
                                    (a_) ** (b_ + c_) :> a ** b + a ** c,
                                    (a_ + b_) ** c_   :> a ** c + b ** c,
                                    (a_ b_) ** c_     :> a ** b ** c,
                                    a_ ** (b_ c_)     :> a ** b ** c
                                }
                            ]
                        ]
                ];

                deltatimes =
                    anticom[gfs[[GFlistIndex, 1]], gfs[[GFlistIndex, 2]]];
                deltatimes = ETjudge[deltatimes];

            ,
                (* truncation: use pre-defined truncation solution *)
                rhs = truncsol[yidong[gfs[[GFlistIndex, dt]], dt], dt];

                If[rhs =!= 0,
                    rhs = FengZhuang[paixu[rhs]];
                ];
            ];

            (* record dt and rhs *)
            solgf[[GFlistIndex, 1]] = dt;
            solgf[[GFlistIndex, 2]] = rhs;

            AppendTo[
                connectionlist,
                loadNewGF[rhs, dt, GFlistIndex]
            ];

            (* solve the equation of motion *)
            If[trid == 0,
                solgf[[GFlistIndex, 3]] =
                    solution[rhs, dt, deltatimes, GFlistIndex, 0],
                solgf[[GFlistIndex, 3]] =
                    solution[rhs, dt, deltatimes, GFlistIndex, 1]
            ];

            GFlistIndex++;
        ];

        (* final EOM system in solgf[[All,3]] *)
        eom = solgf[[All, 3]];

        (* remove zero-GFs and propagate them *)
        del0[];

        kk = Table[{GFnames[[i]], solgf[[i, 3]]}, {i, Length[GFnames]}];
        SuoEOM = Select[kk, #[[2]] =!= 0 && #[[1]] =!= 0 &];

        M = Table[Ling, {Length[SuoEOM]}, {Length[SuoEOM] + 1}];
        L = Range[3];

        Print[
            Length[gfs], " equation(s) finished in ",
            TimeUsed[] - tim, " second(s)."
        ];
    ]


(* ===================== Utility: check identical operators ===================== *)

twoidentical[expr_NonCommutativeMultiply] :=
    Module[{ret = False, i},
        For[i = 1, i < Length[expr], i++,
            If[expr[[i]] === expr[[i + 1]],
                ret = True;
                Break[];
            ];
        ];
        ret
    ]

(* ===================== truncsol: truncation solution ===================== *)

truncsol[expr_Plus, dt_] :=
    Sum[truncsol[expr[[i]], dt], {i, Length[expr]}]

truncsol[expr_Times, dt_] :=
    Product[truncsol[expr[[i]], dt], {i, Length[expr]}]

truncsol[expr_NonCommutativeMultiply, dt_] :=
    Module[{ret = expr, yid, coef, nage},

        yid = yao[expr];

        If[yid > 0,
            If[Length[ret] < 3,
                Print["Error: truncating on a too short expression: ", ret];
                Abort[];
            ];

            If[dt == 1,  (* do the front ones *)
                nage = yaonage[expr, yid][[1]];
                coef = (ret[[1]]*ret[[2]]) /.
                    (trunclist[[yid, 3, nage, 1]]*
                     trunclist[[yid, 3, nage, 2]]) ->
                     trunclist[[yid, 3, nage, 3]];

                If[Length[ret] > 3,
                    ret = coef*ret[[3 ;; -1]],
                    ret = coef*ret[[3]]
                ];
            ];

            If[dt == 2,  (* end ones *)
                nage = yaonage[expr, yid][[1]];
                coef = (ret[[-2]]*ret[[-1]]) /.
                    (trunclist[[yid, 3, nage, 1]]*
                     trunclist[[yid, 3, nage, 2]]) ->
                     trunclist[[yid, 3, nage, 3]];

                If[Length[ret] > 3,
                    ret = coef*ret[[1 ;; -3]],
                    ret = coef*ret[[1]]
                ];
            ];
            ret
        ,
            ret
        ]
    ]

truncsol[expr_, dt_] := expr


(* ===================== yidong: moving operators into truncation position ===================== *)

yidong[expr_Plus, dt_] :=
    Sum[yidong[expr[[i]], dt], {i, Length[expr]}]

yidong[expr_Times, dt_] :=
    Product[yidong[expr[[i]], dt], {i, Length[expr]}]


yidong[expr_NonCommutativeMultiply, 1] :=
    Module[{yid, nage, ret, l1, l2, pos},

        ret = "Undefined";
        yid = yao[expr];

        If[yid != 0,
            {nage, l1, l2} = yaonage[expr, yid];

            If[nage == 0,
                ret = 0,
                (* nage != 0, yidong! *)
                If[inpos1[Length[expr], l1, 1],
                    (* l1 in position, go on with l2 *)
                    If[inpos2[Length[expr], l2, 1],
                        (* l2 in position too, done *)
                        ret = expr,
                        (* l2 not in position, do it *)
                        ret = fermiyi[expr, l2[[1]], 1];
                        ret = yidong[ret, 1];
                    ],
                    (* l1 not in position, do l1 *)
                    ret = fermiyi[expr, l1[[1]], 1];
                    ret = yidong[ret, 1];
                ]
            ]
        ,
            (* yid == 0, no need to yidong *)
            ret = expr
        ];

        If[ret === "Undefined",
            Print["Error: returning value of yidong not defined."];
            Abort[];
        ];

        ret
    ]


yidong[expr_NonCommutativeMultiply, 2] :=
    Module[{yid, nage, ret, l1, l2, pos},

        ret = "Undefined";
        yid = yao[expr];

        If[yid != 0,
            {nage, l1, l2} = yaonage[expr, yid];

            If[nage == 0,
                ret = 0,
                (* nage != 0, yidong! *)
                If[inpos2[Length[expr], l2, 2],
                    (* l2 in position, go on with l1 *)
                    If[inpos1[Length[expr], l1, 2],
                        (* l1 in position too, done *)
                        ret = expr,
                        (* l1 not in position, do it *)
                        ret = fermiyi[expr, l1[[-1]], 2];
                        ret = yidong[ret, 2];
                    ],
                    (* l2 not in position, do l2 *)
                    ret = fermiyi[expr, l2[[-1]], 2];
                    ret = yidong[ret, 2];
                ]
            ]
        ,
            (* yid == 0, no need to yidong *)
            ret = expr
        ];

        If[ret === "Undefined",
            Print["Error: returning value of yidong not defined."];
            Abort[];
        ];

        ret
    ]

yidong[expr_, dt_] := expr


(* ===================== inpos helpers: check if truncation pair is in position ===================== *)

inpos1[len_Integer, l_List, dt_Integer] :=
    Module[{ret = False},
        If[Length[l] == 0,
            Print["Error: inpos1 called with zero length position list."];
            Abort[];
        ];

        If[dt == 1 && l[[1]] == 1,      ret = True];
        If[dt == 2 && l[[-1]] == len - 1, ret = True];

        ret
    ]


inpos2[len_Integer, l_List, dt_Integer] :=
    Module[{ret = False},
        If[Length[l] == 0,
            Print["Error: inpos2 called with zero length position list."];
            Abort[];
        ];

        If[dt == 1 && l[[1]] == 2,     ret = True];
        If[dt == 2 && l[[-1]] == len,  ret = True];

        ret
    ]


(* ===================== fermiyi: fermionic move using commutators ===================== *)

fermiyi[expr_NonCommutativeMultiply, pos_Integer, dt_Integer] :=
    Module[{tmp = expr},

        If[dt == 1,  (* move pos left *)
            If[pos < 2,
                Print["Error: illegal value in fermiyi[", expr, ",", pos, ",", dt, "]"];
                Abort[];
            ];
            tmp[[pos - 1]] =
                com[tmp[[pos - 1]], tmp[[pos]]] - tmp[[pos]] ** tmp[[pos - 1]];
            tmp[[pos]] = 1;
        ];

        If[dt == 2,  (* move pos right *)
            If[pos > Length[expr] - 1,
                Print["Error: illegal value in fermiyi[", expr, ",", pos, ",", dt, "]"];
                Abort[];
            ];
            tmp[[pos]] =
                com[tmp[[pos]], tmp[[pos + 1]]] - tmp[[pos + 1]] ** tmp[[pos]];
            tmp[[pos + 1]] = 1;
        ];

        tmp =
            tmp //. {
                (a_) ** (b_ + c_) :> a ** b + a ** c,
                (a_ + b_) ** c_   :> a ** c + b ** c
            };

        tmp =
            tmp //. {
                (a__) ** 1 ** (b___) :> a ** b,
                (a___) ** 1 ** (b__) :> a ** b
            };

        tmp = ExpandAll[tmp];

        Grab[tmp]
    ]



(* ===================== clearup: map operator strings to GFs ===================== *)

clearup[expr_NonCommutativeMultiply] :=
    Module[{i, tmp, mtpl = 1, ret = expr, pos, p2, p1},

        (* need to find if there's new gf's, or replace with existing ones *)

        i = Length[expr];

        (* there has to be at least one annihilation op, otherwise we're screwed *)
        While[annihilation[expr[[i]]], i--];

        ret = Delete[ret, i];
        ret = AppendTo[ret, expr[[i]]];

        mtpl *= (-1)^(Length[expr] - i);
        (* 我们之所以能这样做是因为 XX 总是排在 XXdag 前面 *)

        p2 = ret[[-1]];

        If[Length[ret] > 2, p1 = ret[[1 ;; -2]]];
        If[Length[ret] == 2, p1 = ret[[1]]];

        If[Length[ret] < 2,
            Print["Error: can't clearup a too short expression:", ret];
            Abort[];
        ];

        pos = Position[gfs, {purepattern[p1], purepattern[p2]}];

        If[Length[pos] > 0,
            i = pos[[1, 1]];
            mtpl*GFnames[[i]] /. corr[gfs[[i, 1]]**gfs[[i, 2]], ret]
        ,
            AppendTo[gfs, {uniquesub[p1], uniquesub[p2]}];
            AppendTo[solgf, {0, 0, 0}];
            AppendTo[
                GFnames,
                OverBar[
                    Unique["GF"] @@ subs[gfs[[-1, 1]]**gfs[[-1, 2]]]
                ]
            ];
            mtpl*GFnames[[-1]] /. corr[gfs[[-1, 1]]**gfs[[-1, 2]], ret]
        ]
    ]

clearup[expr_Plus] :=
    Sum[clearup[expr[[i]]], {i, Length[expr]}]

clearup[expr_Times] :=
    Product[clearup[expr[[i]]], {i, Length[expr]}]

clearup[expr_] := expr


(* ===================== corr: build substitution rules matching operator structure ===================== *)

corr[a_OverHat, b_OverHat] :=
    Module[{},
        If[Length[a[[1]]] != Length[b[[1]]] || ! MatchQ[a, purepattern[b]],
            Print["Error: parameters ", a, " and ", b,
                  " in corr should be identical in form."];
            Abort[];
        ];

        If[Depth[a] == 3,
            Table[a[[1, i]] -> b[[1, i]], {i, Length[a[[1]]]}],
            {}
        ]
    ]

corr[a_NonCommutativeMultiply, b_NonCommutativeMultiply] :=
    Union[
        Flatten[
            Table[corr[a[[i]], b[[i]]], {i, Length[a]}]
        ]
    ]


(* ===================== yao / yaonage: truncation detection helpers ===================== *)

yao[expr_] :=
    Module[{i, ret = 0},
        For[i = 1, i <= Length[trunclist], i++,
            (* for the moment, length is assumed to be 2 later on *)
            If[
                Sum[
                    Count[expr, trunclist[[i, 1, j]]],
                    {j, Length[trunclist[[i, 1]]]}
                ] > trunclist[[i, 2]],
                ret = i;
                Break[];
            ];
        ];
        ret
    ]

yaonage[expr_, yid_] :=
    Module[{l1 = {}, l2 = {}, ret = 0},
        For[i = 1, i <= Length[trunclist[[yid, 3]]], i++,
            l1 = Flatten[Position[expr, trunclist[[yid, 3, i, 1]]]];
            l2 = Flatten[Position[expr, trunclist[[yid, 3, i, 2]]]];

            If[Length[l1] > 0 && Length[l2] > 0,
                ret = i;
                Break[];
            ];
        ];
        (* if ret == 0 then this term should be set to 0 *)
        {ret, l1, l2}
    ]


solution[rhs_, dt_Integer, deltatimes_, GFlistIndex_,1] := Module[{idxIGF, ret = 0,params={},pos,ee}, 
	If[rhs =!= 0,
		If[dt == 1, 
			pos[i_]:=Position[gfs,{purepattern[rhs[[i,1]]],purepattern[gfs[[GFlistIndex,2]]]}][[1,1]];
			ret = Sum[rhs[[i,2]]*
				GFnames[[pos[i]]]/.
					corr[gfs[[pos[i],1]]**gfs[[pos[i],2]],rhs[[i,1]]**gfs[[GFlistIndex,2]]]
				,{i,Length[rhs]}] 
		]; 
		If[dt == 2, 
			pos[i_]:=Position[gfs,{purepattern[gfs[[GFlistIndex,1]]],purepattern[rhs[[i,1]]]}][[1,1]];
			ret = Sum[rhs[[i,2]]*
				GFnames[[pos[i]]]/.
					corr[gfs[[pos[i],1]]**gfs[[pos[i],2]],gfs[[GFlistIndex,1]]**rhs[[i,1]]]
				,{i,Length[rhs]}]
		]; 
		dummy[ret]
	,
		0
	]
]

solution[rhs_, dt_Integer, deltatimes_, GFlistIndex_,0] := Module[{lstRHS, idxIGF, ret = 0,params={},pos,ee,newrhs}, 
	{lstRHS, idxIGF,params} = existself[rhs, dt, GFlistIndex]; 
	(* Print["lstRHS=",lstRHS,"   idxIGF=",idxIGF,"  dt=",dt,"  params=",params]; *)
	If[lstRHS=={} || idxIGF==0, 
		Print["No solution :(  "]
	,
		If[params==={},
			ee=IGFs[[idxIGF,2]] ;
		,
			ee=UnderBar[Apply[Head[IGFs[[idxIGF,2,1]]],params]];  (* to be replaced by "replace" *)
			(* ok when there's only one param *)
		];
		lstRHS=Table[{lstRHS[[i]]},{i,Length[lstRHS]}];
		newrhs=Delete[rhs,lstRHS];
		If[dt == 1, 
			pos[i_]:=Position[gfs,{purepattern[newrhs[[i,1]]],purepattern[gfs[[GFlistIndex,2]]]}][[1,1]];
			ret = Sum[newrhs[[i,2]]*ee*
					GFnames[[pos[i]]]/.
						corr[gfs[[pos[i],1]]**gfs[[pos[i],2]],newrhs[[i,1]]**gfs[[GFlistIndex,2]]]
					,{i,Length[newrhs]}]
		]; 
		If[dt == 2, 
			pos[i_]:=Position[gfs,{purepattern[gfs[[GFlistIndex,1]]],purepattern[newrhs[[i,1]]]}][[1,1]];
			ret = Sum[newrhs[[i,2]]*ee*
					GFnames[[pos[i]]]/.
						corr[gfs[[pos[i],1]]**gfs[[pos[i],2]],gfs[[GFlistIndex,1]]**newrhs[[i,1]]]
					,{i,Length[newrhs]}]
		]; 
		If[deltatimes =!= 0, 
			ret += Grab[ExpandAll[ee*deltatimes]]
		];
	];
	dummy[ret]
]

dummy[0]:=0
dummy[expr_Plus]:=Sum[dummy[expr[[i]]],{i,Length[expr]}]
dummy[expr_]:=Module[{i,ret=expr,tok,l=Length[sumlist]},
	For[i=1,i<=l,i++,
		If[!FreeQ[ret,sumlist[[i]]],
			tok=Unique["j"];
			ret=ret/.sumlist[[i]]->tok;
			AppendTo[sumlist,tok];  (* this one will hurt :(  *)
		]
	];
	ret
]

getparam[expr_Plus]:=Union[Flatten[Table[getparam[expr[[i]]],{i,Length[expr]}]]]
getparam[expr_Times]:=Union[Flatten[Table[getparam[expr[[i]]],{i,Length[expr]}]]]
getparam[expr_]:=If[Depth[expr]==2,Level[expr,1],{}]

existself[rhs_, dt_, GFlistIndex_] := Module[{lstRHS, lstIGF = 0, i,j,params={},coef }, 
	(* tmp = Flatten[Position[rhs, purepattern[gfs[[GFlistIndex,dt]]]]]; *)

	lstRHS=Flatten[  Position[rhs[[All,1]],purepattern[gfs[[GFlistIndex,dt]] ], 1 ]  ];
	If[Length[lstRHS]==0, 
		Print["Warning: this GF cannot derive itself. solution temporarily set to zero."]
	,
		(* go on with the sum of coeff's *)
		coef=ExpandAll[ Total[  rhs[[lstRHS,2]] ] ];
		lstIGF=Flatten[ Position[ IGFs[[All,1]] , purepattern[coef] ,1 ] ];
		If[Length[lstIGF]>1,
			Print["Error: multiple (seudo)IGF's correspond to the same coefficient: ",IGFs[[lstIGF]]," have ",coef];
			Abort[]
		];
		params=getparam[coef];
		If[Length[lstIGF]==1,
			(* IGF found *)
			lstIGF=lstIGF[[1]]
		,
			(* not found, add it *)
			AppendTo[IGFs,{coef,UnderBar[Unique["gi"]@@params  ]  }];
			lstIGF=Length[IGFs]
		]			
	];

(*	If[Length[params]>1,
		Print["Temporary Error: more than one parameters not supported for isolated GF now. ",params];
	];  *)
	{lstRHS,lstIGF,params}
]

loadNewGF[0,a__]:={}
loadNewGF[rhs_List, dt_Integer, GFlistIndex_] := Module[{i, c = 0,op}, 
	If[dt != 1 && dt != 2, Print["wth?? dt=", dt]]; 
	For[i = 1, i <= Length[rhs], i++, 
		If[dt == 1 && FreeQ[gfs, {purepattern[rhs[[i,1]]], purepattern[gfs[[GFlistIndex,2]]]}], 
			op={uniquesub[rhs[[i,1]]], uniquesub[gfs[[GFlistIndex,2]]]};
			AppendTo[gfs,op]; 
			AppendTo[solgf, {0, 0, 0}]; 
			AppendTo[GFnames, OverBar[Unique["GF"]@@subs[gfs[[-1,1]]**gfs[[-1,2]] ] ] ];
			c++
		]; 
		If[dt == 2 && FreeQ[gfs, {purepattern[gfs[[GFlistIndex,1]]], purepattern[rhs[[i,1]]]}], 
			op={uniquesub[gfs[[GFlistIndex,1]]], uniquesub[rhs[[i,1]]]};
			AppendTo[gfs,op];
			AppendTo[solgf, {0, 0, 0}];
			AppendTo[GFnames, OverBar[Unique["GF"]@@subs[gfs[[-1,1]]**gfs[[-1,2]] ] ] ];
			c++
		]; 
	]; 
	(* \:8fd9\:91cc\:6211\:4eec\:8981\:8fd4\:56de\:4e00\:4e2a\:65b0\:683c\:6797\:51fd\:6570\:8868 *)
	If[Length[gfs]!=Length[solgf],Print["Error: Length of gfs and solgf not equal. ",Length[gfs]," and ",Length[solgf]];
		Abort[] ];
(*Print["tick3"];*)
	If[dt==1,
		Cases[ Table[Flatten[Position[gfs,{purepattern[rhs[[i,1]]],purepattern[gfs[[GFlistIndex,2]]]}]] [[1]],{i,Length[rhs]}], Except[GFlistIndex]    ]
	,
		Cases[ Table[Flatten[Position[gfs,{purepattern[gfs[[GFlistIndex,1]]],purepattern[rhs[[i,1]]]}]] [[1]],{i,Length[rhs]}], Except[GFlistIndex]    ]
	]
]

subscriptedQ[op_OverHat] := If[Depth[op] == 2, False, True]
subscriptedQ[op_] := If[Depth[op] == 1, False, True]
script2blank[op_OverHat] := If[subscriptedQ[op], OverHat[op[[1,0]] @@ Table[_, {Length[op[[1]]]}]], op]
script2unique[op_OverHat] := If[subscriptedQ[op], OverHat[op[[1,0]] @@ Table[Unique["i"], {Length[op[[1]]]}]], op]

purepattern[expr_OverHat] := script2blank[expr]; 
purepattern[expr_NonCommutativeMultiply] := NonCommutativeMultiply @@ Table[script2blank[expr[[i]]], {i, Length[expr]}]
purepattern[expr_Plus]:=Sum[purepattern[expr[[i]]],{i,Length[expr]}]
purepattern[expr_Times]:=Product[purepattern[expr[[i]]],{i,Length[expr]}]
purepattern[expr_UnderBar]:=UnderBar[purepattern[expr[[1]]]]
(*purepattern[expr_OverBar]:=If[Depth[expr]==3,OverBar[Apply[expr[[1,0]],Table[Blank[],{Length[expr[[1]]]}]]],expr]*)
purepattern[expr_OverBar]:=OverBar[purepattern[expr[[1]] ]  ]
purepattern[expr_OverTilde]:=OverTilde[purepattern[expr[[1]] ]  ]
purepattern[expr_] := If[Depth[expr] >= 2, expr[[0]] @@ Table[_, {Length[expr]}], expr]

uniquesub[expr_OverHat] := script2unique[expr]; 
uniquesub[expr_NonCommutativeMultiply] := NonCommutativeMultiply @@ Table[script2unique[expr[[i]]], {i, Length[expr]}]

shoulong[expr_Plus]:=Sum[ shoulong[expr[[i]] ],{i,Length[expr]} ]
shoulong[expr_Times]:=Product[ shoulong[expr[[i]] ],{i,Length[expr] } ]
shoulong[expr_NonCommutativeMultiply]:=If[twoidentical[expr],0,expr]
shoulong[expr_]:=expr

anticom[a_, b_] := Module[{kk}, 
	kk = anticommutator[a, b]//ExpandAll;
	kk=Grab[kk];
	kk=paixu[kk];
	shoulong[kk]
]

com[a_, b_] := Module[{kk}, 
	kk = commutator[a, b]//ExpandAll;
	kk=Grab[kk];
	kk=paixu[kk];
	shoulong[kk]
]

com2[a_,b_]:=Module[{kk},kk=commutator[a,b]//ExpandAll;Grab[kk] ]
Grab[expr_]:=Module[{tt},
	tt=grab[expr];   (* grab for getting **'s out and sum up delta's; there should be no Plus within parenthases *)
	grab3[tt]	(* grab3 for adding out kroneckerdelta's  ??? why ????  *)
]

grab[kk_] := Module[{terms, s, pos, t, lst, token, i, j, th}, 
	terms = {}; 
	If[kk[[0]] == Plus, 
		For[i = 1, i <= Length[kk], i++, 
			t = kk[[i]]; 
			pos = Position[t, OverHat]; 
			lst = Table[pos[[ti,1 ;; -2]], {ti, Length[pos]}]; 
			s = {}; 
			For[j = 1, j <= Length[lst], j++, 
				AppendTo[s, Extract[t, lst[[j]]]]
			]; 
			If[Length[s] > 1, s[[0]] = NonCommutativeMultiply]; 
			If[Length[s] == 1, s[[0]] = Times]; 
			t = Delete[t, lst]; 
			t = t //. NonCommutativeMultiply -> Times; 
			t = t*s; 
(*			For[j = 1, j <= Length[sumlist], j++, 
				token = sumlist[[j]]; 
				If[summable[t, token] == True, 
					t=Integrate[t,{token,-Infinity,Infinity},Assumptions->Element[Level[t,{-1}],Reals]];
				]
			]; *)
			AppendTo[terms, t]; 
		]; 
		terms[[0]] = Plus
	]; 
	
	If[kk[[0]] == Times || kk[[0]] == NonCommutativeMultiply, 
		th = kk[[0]]; 
		t = kk; 
		pos = Position[t, OverHat]; 
		lst = Table[pos[[ti,1 ;; -2]], {ti, Length[pos]}];
		s = {}; 
		For[j = 1, j <= Length[lst], j++, 
			AppendTo[s, Extract[t, lst[[j]]]]
		]; 
		If[Length[s] > 1, s[[0]] = NonCommutativeMultiply]; 
		If[Length[s] == 1, s[[0]] = Times]; 
		t = Delete[t, lst]; 
		t = t //. NonCommutativeMultiply -> Times; 
		t = t*s; 
(*		For[j = 1, j <= Length[sumlist], j++, 
			token = sumlist[[j]]; 
			If[summable[t, token] == True, 
				t=Integrate[t,{token,-Infinity,Infinity},Assumptions->Element[Level[t,{-1}],Reals]];
			]
		]; *)
		AppendTo[terms, t]; 
		If[Length[terms] > 1, terms[[0]] = th, terms[[0]] = Times]; 
	]; 
	If[terms == {}, terms = kk]; 
	terms
]
grab2[expr_Plus]:=Sum[grab2[expr[[i]]],{i,Length[expr]}]
grab2[expr_Times]:=Product[grab2[expr[[i]]],{i,Length[expr]}]
grab2[expr_NonCommutativeMultiply]:=Module[{times={},nt={},i},
	For[i=1,i<=Length[expr],i++,
		If[Head[expr[[i]]]===OverHat,
			AppendTo[nt,expr[[i]]]
		,
			AppendTo[times,expr[[i]]]
		]
	];
	If[Length[nt]>1,
		Times@@times * NonCommutativeMultiply@@nt
	,
		If[Length[nt]==1,
			Times@@times * nt[[1]]
		,
			Times@@times
		]
	]
]

grab2[expr_]:=expr
grab3[expr_Plus]:=Sum[grab3[expr[[i]]],{i,Length[expr]}]
grab3[expr_Times]:=Module[{i,te=expr,j,pospow},
(*	If[FreeQ[expr,Power],
		For[i=1,i<=Length[sumlist],i++,
			If[summable[te,sumlist[[i]] ],
				te=Integrate[te,{sumlist[[i]],-Infinity,Infinity},Assumptions->Element[Level[te,{-1}],Reals]];
			]
		];
		te
	,
		pospow=Flatten[Position[expr,_Power,1]];  
		If[Length[pospow]==0,
			Print["Error: this must be a mathematica bug :("];
			Abort[]
		];
		grab3[Delete[expr,Table[{pospow[[j]]},{j,Length[pospow]}] ]]*
			Product[Power[grab3[ expr[[pospow[[j]],1]]],expr[[ pospow[[j]],2]]  ],{j,Length[pospow]} ]
	] *)
	For[i=1,i<=Length[sumlist],i++,
		If[summable[te,sumlist[[i]] ],
			te=Integrate[te,{sumlist[[i]],-Infinity,Infinity},Assumptions->Element[Level[te,{-1}],Reals]];
		]
	];
	te
]

(*grab3[expr_Power]:=Power[grab3[ expr[[1]] ], expr[[2]] ]*)
grab3[e_]:=e
summable[t_, token_] := Module[{i, j, t1, t2, k1, k2, res = False}, 
	If[FreeQ[sumlist, token] == False, 
		k1 = Position[t, token]; 
		k2 = Position[t, DiracDelta]; 
		For[i = 1, i <= Length[k1], i++, 
			For[j = 1, j <= Length[k2], j++, 
				t1 = k1[[i,1 ;; Length[k2[[j]]] - 1]]; 
				t2 = k2[[j,1 ;; Length[k2[[j]]] - 1]]; 
				If[t1 == t2, res = True; ]
			]
		]
	]; 
	res
]

privatecomm[a_, b_] := Module[{t = 0, i}, 
	(* rulelist[[i,4]]: 1 means fermion and 0 means boson. this is right! {a,b}={b,a} while [a,b]=-[b,a] *)
	(* for some weird reasons, Which did not work here. *)
	For[i = 1, i <= Length[rulelist], i++, 
		If[a == rulelist[[i,1]] && b == rulelist[[i,2]], t = rulelist[[i,3]]; Break[]]; 
		If[b == rulelist[[i,1]] && a == rulelist[[i,2]] && rulelist[[i,4]]==0, t = -rulelist[[i,3]]; Break[]]; 
		If[b == rulelist[[i,1]] && a == rulelist[[i,2]] && rulelist[[i,4]]==1, t = rulelist[[i,3]]; Break[]]; 
		If[Head[a] == Head[rulelist[[i,1]]] && Head[b] == Head[rulelist[[i,2]]] && Head[a] =!= Symbol, 
			t = a*b /. rulelist[[i,1]] rulelist[[i,2]]->rulelist[[i,3]]; Break[]
		]; 
		If[Head[a] == Head[rulelist[[i,2]]] && Head[b] == Head[rulelist[[i,1]]] && 
				Head[a] =!= Symbol && rulelist[[i,4]]==0 , 
			t = (-b)*a /. rulelist[[i,1]] rulelist[[i,2]]->rulelist[[i,3]]; Break[]
		]; 
		If[Head[a] == Head[rulelist[[i,2]]] && Head[b] == Head[rulelist[[i,1]]] && 
				Head[a] =!= Symbol && rulelist[[i,4]]==1 , 
			t = (b)*a /. rulelist[[i,1]] rulelist[[i,2]]->rulelist[[i,3]]; Break[]
		]; 
	]; 
	t
]

commutator[a_Plus,b_Plus]:=Sum[commutator[a[[i]],b[[j]] ],{i,Length[a]},{j,Length[b]}]
commutator[a_Plus,b_]:=Sum[commutator[a[[i]],b],{i,Length[a]}]
commutator[a_,b_Plus]:=Sum[commutator[a,b[[i]]],{i,Length[b]}]
commutator[a_OverHat,b_OverHat]:=privatecomm[a[[1]],b[[1]]]
commutator[a_OverHat,b_NonCommutativeMultiply]:=paixu[a**b-b**a]
commutator[a_NonCommutativeMultiply,b_OverHat]:=paixu[a**b-b**a]
commutator[a_NonCommutativeMultiply,b_NonCommutativeMultiply]:=paixu[a**b-b**a]
commutator[a_Times,b_]:=Module[{pos},
	If[!FreeQ[a,OverHat],pos=Position[a,_OverHat]];
	If[!FreeQ[a,NonCommutativeMultiply],pos=Position[a,_NonCommutativeMultiply]];
	If[Length[pos]>1,
		Print["Error: operators must be non-commutatively arranged in ",a];
		Abort[];
	];
	Delete[a,pos]*commutator[Extract[a,pos][[1]],b]
]
commutator[a_,b_Times]:=Module[{pos},
	If[!FreeQ[b,OverHat],pos=Position[b,_OverHat]];
	If[!FreeQ[b,NonCommutativeMultiply],pos=Position[b,_NonCommutativeMultiply]];
	If[Length[pos]>1,
		Print["Error: operators must be non-commutatively arranged in ",b];
		Abort[];
	];
	Delete[b,pos]*commutator[a,Extract[b,pos][[1]]]
]

anticommutator[a_Plus,b_Plus]:=Sum[commutator[a[[i]],b[[j]] ],{i,Length[a]},{j,Length[b]}]
anticommutator[a_Plus,b_]:=Sum[commutator[a[[i]],b],{i,Length[a]}]
anticommutator[a_,b_Plus]:=Sum[commutator[a,b[[i]]],{i,Length[b]}]
anticommutator[a_OverHat,b_OverHat]:=privatecomm[a[[1]],b[[1]]]
anticommutator[a_OverHat,b_NonCommutativeMultiply]:=paixu[a**b+b**a]
anticommutator[a_NonCommutativeMultiply,b_OverHat]:=paixu[a**b+b**a]
anticommutator[a_NonCommutativeMultiply,b_NonCommutativeMultiply]:=paixu[a**b-b**a]
anticommutator[a_Times,b_]:=Module[{pos},
	If[!FreeQ[a,OverHat],pos=Position[a,_OverHat]];
	If[!FreeQ[a,NonCommutativeMultiply],pos=Position[a,_NonCommutativeMultiply]];
	If[Length[pos]>1,
		Print["Error: operators must be non-commutatively arranged in ",a];
		Abort[];
	];
	Delete[a,pos]*commutator[Extract[a,pos][[1]],b]
]
anti
commutator[a_,b_Times]:=Module[{pos},
	If[!FreeQ[b,OverHat],pos=Position[b,_OverHat]];
	If[!FreeQ[b,NonCommutativeMultiply],pos=Position[b,_NonCommutativeMultiply]];
	If[Length[pos]>1,
		Print["Error: operators must be non-commutatively arranged in ",b];
		Abort[];
	];
	Delete[b,pos]*commutator[a,Extract[b,pos][[1]]]
]

Commutator[A_, B_] := Module[{tmp = 0, tn, did, biaochengfa, pos, branch, i, j, coe}, 
	If[Head[A] == Plus, tmp = Sum[Commutator[A[[i]], B], {i, Length[A]}]  ]; 
	If[Head[A] == Times, 
		tmp = A[[1]]**Commutator[Times[A[[2 ;; Length[A]]]], B] - 
			Commutator[B, A[[1]]]**(Times[A[[2 ;; Length[A]]]])
	]; 
	If[Head[A] == NonCommutativeMultiply, 
		tn = NonCommutativeMultiply[A[[2 ;; Length[A]]]]; 
		If[Length[tn] == 1, tn = tn[[1]]]; 
		tmp = A[[1]]**Commutator[tn, B] - Commutator[B, A[[1]]]**tn
	]; 
	If[Head[B] == Plus, tmp = Sum[Commutator[A, B[[i]]], {i, Length[B]}]  ]; 
	If[Head[B] == Times, 
		tmp = Commutator[A, B[[1]]]**(Times[B[[2 ;; Length[B]]]]) - 
			B[[1]]**Commutator[Times[B[[2 ;; Length[B]]]], A]
	]; 
	If[Head[B] == NonCommutativeMultiply, 
		tn = NonCommutativeMultiply[B[[2 ;; Length[B]]]]; 
		If[Length[tn] == 1, tn = tn[[1]]]; 
		tmp = Commutator[A, B[[1]]]**tn - B[[1]]**Commutator[tn, A]
	]; 
	If[Head[B] == Plus, tmp = Sum[Commutator[A, B[[i]]], {i, Length[B]}]  ]; 
	If[Head[A] == OverHat && Head[B] == OverHat, tmp = privatecomm[A[[1]], B[[1]] ]  ]; 
	tmp = Expand[tmp]; 
	Print["ceng jing: ", A,"  ",B,"   ",tmp];
	tmp //. {(a_)**((b_) + (c_)) :> a**b + a**c, ((a_) + (b_))**(c_) :> a**c + b**c,(a_ b_)**c_:>a**b**c, a_**(b_ c_):>a**b**c,(b___)**0**(a___) :> 0 }
]
paixu[expr_NonCommutativeMultiply] := Module[{i = 1, tmp = expr, ret = expr}, 
	While[i < Length[expr] && OrderedQ[{expr[[i]], expr[[i + 1]]}], i++]; 
	If[i < Length[expr], 
		(* for safety, here we can replace tmp's head with list and then put it back *)
		tmp[[i]] = privatecomm[expr[[i,1]], expr[[i + 1,1]]] - expr[[i + 1]]**expr[[i]];  (* this applies only to fermions *)
		tmp[[i + 1]] = 1; 
		tmp = tmp //. {(a__)**1**(b___) :> a**b , (a___)**1**(b__) :> a**b }; 
		If[Length[tmp]==1, tmp=tmp[[1]] ];
		tmp = tmp //. {(b___)**0**(a___) :> 0}; 
		tmp = tmp //. {(a_)**((b_) + (c_)) :> a**b + a**c, ((a_) + (b_))**(c_) :> a**c + b**c}; 
		tmp = grab[tmp]; 
		ret = paixu[tmp]
	]; 
	ret
]
paixu[expr_Plus] := Sum[paixu[expr[[i]]], {i, Length[expr]}]
paixu[expr_Times] := Product[paixu[expr[[i]]], {i, Length[expr]}]
paixu[expr_] := expr

End[]; 
EndPackage[]; 
