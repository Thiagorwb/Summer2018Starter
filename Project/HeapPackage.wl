(* ::Package:: *)

BeginPackage["MinHeap`"]


MinHeapQ::usage="MinHeapQ on [heap_List] will return if heap is a MinHeap or not" ;


MinHeapQ[heap_List]:=And@@Table[heap[[Floor[i/2]]]<= heap[[i]], {i, 2, heap//Length}];


HeapifyDown::usage="HeapifyDown on [heap, i] will modify the heap in place, swapping the element originally at position i downwards on the tree until the Min-Heap property is satified";


HeapifyDown:=Function[{heap, i},
With[{n = heap//Length},
Which[ 
	n< 2i,
		heap,
	(*at leaf*)
	
	n<=2i && heap[[i]]>= heap[[2i]], 
		{heap[[i]], heap[[2i]]}={heap[[2i]], heap[[i]]};
		HeapifyDown[heap, 2i];,
	(*only left child*)
	
	n<=2i && heap[[i]]<=  heap[[2i]], 
		heap,
	(*only left child, satisfied*)
	
	heap[[i]]<= heap[[2i]] && heap[[i]]<= heap[[2i+1]], 
		heap,
	(*property satisfied*)
	
	heap[[i]]>=Min[heap[[2i]], heap[[2i+1]]] && heap[[2i]]<=  heap[[2i+1]],
		{heap[[i]], heap[[2i]]}={heap[[2i]], heap[[i]]};
		HeapifyDown[heap, 2i];,
	(*swap with left child*)
	
	heap[[i]]>=  Min[heap[[2i]], heap[[2i+1]]] && heap[[2i]]>heap[[2i+1]],
		{heap[[i]], heap[[2i+1]]}={heap[[2i+1]], heap[[i]]};
		HeapifyDown[heap, 2i+1];
	(*swap with right child*)
 ]
 ],
 HoldFirst
]


HeapifyUp::usage="HeapifyUp on [heap, i] will modify the heap in place, swapping the element originally at position i upwards on the tree until the Min-Heap property is satified";


HeapifyUp:=Function[{heap, i},
Which[
i==1,
	heap,
(*at root*)

heap[[i]]>= heap[[Floor[i/2]]],
	heap,
(*satisfies minHeap prop, return*)

heap[[i]]<= heap[[Floor[i/2]]],
	{heap[[i]], heap[[Floor[i/2]]]}={heap[[Floor[i/2]]], heap[[i]]};
	HeapifyUp[heap, Floor[i/2]];
(*swap with parent, if greater*)
],
HoldFirst
]


HInsert::usage="HInsert on [heap, element] will insert element into the tree using HeapifyUp";


HInsert:=Function[{heap, element},
AppendTo[heap, element];
HeapifyUp[heap, heap//Length];,
HoldFirst
]


BuildH::usage="BuildH on [list] will modify list into a Min-Heap";


BuildH:=Function[{list},
Map[HeapifyDown[list, #]&, Range[Floor[(list//Length)/2], 1, -1]];,
HoldFirst
]


HExtractMin::usage="HExtractMin on [heap] will output the minimum element in the heap, and delete it using an amortized algorithm. Until the amortization step, it will leave null elements (\[Infinity]) in the MinHeap. It requires a global counter \!\(\*
StyleBox[\"dcount\",\nFontSlant->\"Italic\"]\)";


Begin["Private`"];


dcount=0;


End[];


HExtractMin:=Function[{heap}, Block[ {n = heap//Length, x = heap[[1]]},

(*increment delete counter*)
dcount++;

(*swap last element*)
{heap[[1]], heap[[n]]}={heap[[n]], heap[[1]]};

(*set infinity at the end*)
heap[[n]] = Infinity;

(*divide into amortization cases*)
If[dcount > n / 2, 
	dcount = 0; 
	heap = Select[heap, #!= Infinity&];
	BuildH[heap];
];

(*Corrects swapped position*)
HeapifyDown[1];

(*output minimum*)
x
],
HoldFirst
]


EndPackage[]
