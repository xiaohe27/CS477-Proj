class Data {}
class INode 
{
ghost var tailContents: seq<Data>;
ghost var spine: seq<INode>;
ghost var footprint: set<INode>;

var data: Data;
var next: INode;


function method len():int
requires Valid();
reads this, footprint;
ensures len() == |footprint| == |tailContents| + 1;
{
if next == null then 1 else 1 + next.len()
}



predicate good()
reads this, footprint;
{
    this in footprint 
	&& (next != null ==> (next in footprint 
	&& this !in next.footprint 
	&& footprint == {this} + next.footprint
	&& spine == [this] + next.spine
	&& tailContents == [next.data] + next.tailContents
	))
	&& (next ==null ==> tailContents == [] && footprint == {this}
				&& spine == [this])
}


predicate Valid()
reads this, footprint;
{
good()  
&& (next != null ==> next.Valid())
}


predicate ValidLemma()
requires Valid();
reads this, footprint;
ensures ValidLemma();
ensures (forall nd :: nd in spine ==> nd in footprint);
ensures |tailContents| == |footprint|-1 == |spine|-1;
ensures forall nd :: nd in spine ==> nd != null && nd.Valid();
ensures forall nd :: nd in footprint ==> nd != null && nd.Valid();
{
if next == null then (spine == [this])
else (
spine == [this] + next.spine 
&& next.ValidLemma())
}


method hasPathTo(tarNd:INode) returns (hasPath:bool)
	requires tarNd != null;
	requires Valid();
	modifies {};
	ensures Valid();
	ensures hasPath <==> tarNd in footprint;
{
	var index := indexOf(tarNd);

	if (index == -1) {hasPath := false;}
	else {hasPath := true;}

	return hasPath;
}


method indexOf(tarNd:INode) returns (pos:int)
	requires tarNd != null;
	requires Valid();

	modifies {};
	ensures Valid();
	ensures |footprint| == |spine| == |tailContents| + 1;
	ensures
 tarNd in footprint <==> (
		0 <= pos < |footprint|
  && spine[pos] == tarNd
	&& if pos == 0 then tarNd.data == data
else tarNd.data == tailContents[pos-1]);

	ensures tarNd !in footprint <==> pos == -1;
{

var curNd := this;
pos := 0;

assert ValidLemma();
assert ndValid2ListValidLemma();

var length := len();

while(pos < length)
invariant 0 <= pos <= length;
invariant pos != length ==> spine[pos] == curNd;
invariant curNd != null ==> curNd.Valid();
invariant (curNd != null &&  tarNd in curNd.footprint) <==> tarNd in footprint;
invariant curNd != null ==> ( length == pos + |curNd.footprint| == |tailContents| + 1);
{
	if (tarNd == curNd)
	{
assert spineTCLemma();
return pos;
	}
	
	curNd := curNd.next;
	pos := pos + 1;
}

assert tarNd !in footprint;
return -1;
}


predicate ndValid2ListValidLemma()
requires Valid();
reads this, footprint;

ensures ndValid2ListValidLemma();
ensures forall nd :: nd in spine ==> nd in footprint;
ensures forall nd :: nd in footprint ==> nd != null && nd.footprint <= footprint;

ensures validSeqCond(spine);
{
if next == null then (spine == [this] && footprint == {this}
					&& tailContents == [])
else (
this !in next.footprint &&
spine == [this] + next.spine 
&& footprint == {this} + next.footprint
&& tailContents == [next.data] + next.tailContents
&& next.ndValid2ListValidLemma())
}

predicate spineTCLemma()
	requires Valid();
	reads this, footprint;
	ensures spineTCLemma();
	ensures |spine| == |tailContents| + 1;
	ensures null !in spine;
     ensures spine[0].data == this.data &&
		forall i :: 0 < i < |spine| ==> spine[i].data == this.tailContents[i-1];
{
	if next == null then true
	else spine == [this] + next.spine && tailContents == [next.data] + next.tailContents
		&& next.spineTCLemma()
}
////////////////////////////////////////////////////////

function getFtprint(nd:INode): set<INode>
reads nd;
{
if nd == null then {} else nd.footprint
}

function sumAllFtprint(mySeq: seq<INode>): set<INode>
reads mySeq;
ensures forall nd :: nd in mySeq ==> 
	(nd != null ==> nd.footprint <= sumAllFtprint(mySeq));
{
if mySeq == [] then {} else getFtprint(mySeq[0]) + sumAllFtprint(mySeq[1..])
}

///////////////////////////////////////////

predicate listInv(mySeq: seq<INode>)
reads mySeq, (set nd | nd in mySeq);
{
null !in mySeq && (forall nd :: nd in mySeq ==> nd in nd.footprint) &&
(forall i :: 0 <= i < |mySeq|-1 ==> mySeq[i].next == mySeq[i+1])
&& (forall i, j :: 0 <= i < j < |mySeq| ==> mySeq[i] !in mySeq[j].footprint)
}

predicate listCond(mySeq: seq<INode>)
reads mySeq, (set nd | nd in mySeq);
{
null !in mySeq && (forall nd :: nd in mySeq ==> nd in nd.footprint) &&
(forall i :: 0 <= i < |mySeq|-1 ==> mySeq[i].next == mySeq[i+1]
	&& mySeq[i].footprint == {mySeq[i]} + mySeq[i+1].footprint
	&& mySeq[i].tailContents == [mySeq[i+1].data] + mySeq[i+1].tailContents
	&& mySeq[i].spine == [mySeq[i]] + mySeq[i+1].spine)
	&& (forall i, j :: 0 <= i < j < |mySeq| ==> mySeq[i] !in mySeq[j].footprint)

	&& (forall i :: 0 <= i < |mySeq| ==> |mySeq|-i <= |mySeq[i].spine|)
&& (forall i :: 0 <= i < |mySeq| ==> |mySeq|-i-1 <= |mySeq[i].tailContents|)
}


predicate validSeqCond(mySeq: seq<INode>)
reads mySeq, (set nd | nd in mySeq);
{
listCond(mySeq) 
&& (mySeq != [] ==> mySeq[|mySeq|-1].next == null
&& mySeq[|mySeq|-1].footprint == {mySeq[|mySeq|-1]}
&& mySeq[|mySeq|-1].tailContents == []
&& mySeq[|mySeq|-1].spine == [mySeq[|mySeq|-1]])
}


}

//The INodes class: a list
class INodes {
  var head: INode;

  ghost var contents: seq<Data>;
  ghost var footprint: set<object>;
  ghost var spine: set<INode>;

predicate valid()
reads this, footprint; 
{
this in footprint 
&& spine <= footprint
&& head in spine 
&&
(forall nd :: nd in spine ==> (nd != null && nd.footprint <= footprint - {this})) 
&&
(forall nd :: nd in spine ==> nd != null && nd.Valid())

&&
(forall nd :: nd in spine ==> (nd.next != null ==> nd.next in spine))

&& contents == head.tailContents
&& head.footprint == spine
}


//////////////////////////////////

method contains(tarNd:INode) returns (isIn:bool)
	requires valid();
	requires tarNd != null;
	modifies {};
	ensures valid();
	ensures isIn <==> tarNd in head.footprint;
{
isIn := head.hasPathTo(tarNd);
}


method indexOf(tarNd:INode) returns (index:int)
	requires valid();
	requires tarNd != null && tarNd != head && {tarNd} * footprint <= head.footprint;
	modifies {};

	ensures footprint == old(footprint);
	ensures valid();
	ensures tarNd !in footprint <==> index == -1;
	ensures tarNd in footprint 
	 <==> (
		0 <= index < |head.spine| - 1
  && head.spine[index+1] == tarNd
	&& |contents| == |head.tailContents| == |head.spine| - 1
	&& tarNd.data == contents[index] );

{
	index := head.indexOf(tarNd);

	assert index > 0 || index == -1;
	if(index != -1) {
		index := index - 1;
	} else {}
}



}
