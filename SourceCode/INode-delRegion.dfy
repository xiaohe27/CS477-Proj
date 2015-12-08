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

predicate validSeqContentsLemma()
	requires Valid();
	reads this, footprint;
	ensures validSeqContentsLemma();
	ensures validSeqCond(spine);
	ensures |tailContents| == |footprint|-1 == |spine|-1;
  ensures forall i :: 0 <= i < |spine| ==> spine[i].data == ([data] + tailContents)[i];
	ensures forall i :: 0 <= i < |spine| ==> spine[i].tailContents ==  ([data] + tailContents)[i+1..];
{
	ndValid2ListValidLemma() &&
		next != null ==> next.validSeqContentsLemma()
}

method contains(tarNd:INode) returns (isIn:bool)
	requires tarNd != null;
	requires Valid();
	modifies {};
	ensures Valid();
	ensures isIn <==> tarNd in footprint;
	decreases footprint;
{
	if (this == tarNd) {isIn := true;}
	else {
		if (next == null) {isIn := false;}
		else {isIn := next.contains(tarNd);}
	}
}

predicate fpLemma(tarNd:INode)
	requires Valid();
	requires tarNd in footprint;
	reads this, footprint;
ensures fpLemma(tarNd);
	ensures tarNd != null && tarNd.next != null ==> tarNd.next in footprint;
{
	if this == tarNd then true
	else if next != null then next.fpLemma(tarNd)
		else false
}

method indexOf(tarNd:INode) returns (index:int)
	requires tarNd != null;
	requires Valid();
	requires tarNd in footprint - {this};
	
	modifies {};
	ensures Valid();
	ensures |footprint| == |spine| == |tailContents| + 1;
	ensures
		0 < index < |footprint|
  && spine[index] == tarNd
	&&  tarNd.data == tailContents[index-1];
{

var curNd := this;
index := 0;

assert ValidLemma();
assert ndValid2ListValidLemma();

var length := len();

while(index < length)
invariant 0 <= index <= length;
invariant index != length ==> spine[index] == curNd;
invariant curNd != null ==> curNd.Valid();
invariant (curNd != null &&  tarNd in curNd.footprint) <==> tarNd in footprint;
invariant curNd != null ==> ( length == index + |curNd.footprint| == |tailContents| + 1);
{
	if (tarNd == curNd)
	{
assert spineTCLemma();
return index;
	}
	
	curNd := curNd.next;
	index := index + 1;
}

assert false;
}

/////////////////////////////////////////

method delete(pos:int) returns (delNd:INode)
requires Valid();
requires 0 < pos <= |tailContents|;

modifies footprint;

ensures Valid();
ensures [data] + tailContents == old(([data] + tailContents)[0..pos] + ([data] + tailContents)[pos+1..] );
ensures footprint == old(footprint) - {delNd};
ensures old(|tailContents| == |spine| - 1 && 0 < pos < |spine|);
ensures delNd == old(spine[pos]);

//new
ensures delNd != null;
{
var curNd := this;
var curIndex := 0;

assert ValidLemma();
assert ndValid2ListValidLemma();
assert validSeqContentsLemma();
assert validSeqTCLemma(spine);

while (curIndex < pos-1)
invariant 0 <= curIndex < pos;
invariant curNd != null && curNd.Valid();
invariant validSeqCond(spine);
invariant |curNd.tailContents| + curIndex == |tailContents|;
invariant curNd.next != null;
invariant curNd == spine[curIndex];

invariant  spine[curIndex].data == ([data] + tailContents)[curIndex];

invariant curNd.next == spine[curIndex+1];
invariant curNd.next.next != null ==> curNd.next.next == spine[curIndex+2];

modifies {};
{
curNd := curNd.next;
curIndex := curIndex + 1;
}

delNd := curNd.next;

delNext(curNd, delNd, pos);


if(1 < pos <= |tailContents|) {
ghost var oldContents := old([data] + tailContents); 
ghost var newSpine := spine[0..pos-1];

assert |oldContents| == old(|tailContents| + 1);

assert shrinkLemma(spine, pos, oldContents);

assert delNd != null;

updateSeq4Del(newSpine, delNd, pos, curNd, oldContents, this);

} else {}
 

}

////////////////////////////////////////////////////////
method delNext(curNd: INode, delNd:INode, pos:int)
  requires curNd != null && curNd.Valid();
  requires curNd.next == delNd && delNd != null && delNd.Valid();
	requires Valid();
  requires 0 < pos < |spine| && spine[pos-1] == curNd;
  requires validSeqCond(spine);

	requires forall i :: 0 <= i <= pos-2 ==>
	(|spine[i].tailContents|) >= pos - i;
	requires |tailContents| >= pos;

	requires curNd.data == ([data] + tailContents)[pos-1];
	requires curNd.tailContents == ([data] + tailContents)[pos..];

	requires |tailContents| == |spine|-1;
	requires forall i :: 0 <= i <= pos-2 ==> spine[i].data == ([data] + tailContents)[i];

//new
requires	 (forall nd :: nd in spine ==> nd in footprint);
	modifies curNd;
	
	ensures curNd.Valid();
	ensures curNd.data == old(curNd.data) && curNd.next == delNd.next;
	ensures curNd.footprint == old(curNd.footprint) - {delNd};
	ensures curNd.tailContents == old(curNd.tailContents[1..]);
	ensures curNd.spine == old([curNd.spine[0]] + curNd.spine[2..]);

	ensures forall i :: 0 <= i <= pos-2 ==> spine[i].data == old(spine[i].data) &&
		spine[i].next == old(spine[i].next) &&
		spine[i].tailContents == old(spine[i].tailContents) &&
		spine[i].footprint == old(spine[i].footprint) &&
		spine[i].spine == old(spine[i].spine);

		ensures listInv(spine[0..pos]);
		ensures listCond(spine[0..pos-1]); 


		ensures pos > 1 ==> spine[pos-2].tailContents == [curNd.data] + [delNd.data] + curNd.tailContents;

		//new
		ensures pos > 1 ==> spine[pos-2].footprint == {spine[pos-2]} + curNd.footprint + {delNd};

	ensures forall i :: 0 <= i <= pos-2 ==>
		(|spine[i].tailContents|) >= pos - i;

		//	ensures pos > 1 ==>  footprint == old(footprint) && (set nd | nd in spine) <= old(footprint);

		ensures pos > 1 ==>  footprint == old(footprint) &&
		spine == old(spine) && (forall nd :: nd in spine ==> nd in footprint);
				
			ensures	curNd.tailContents == old([data] + tailContents)[pos+1..];
			
			ensures forall i :: 0 <= i <= pos-2 ==> spine[i].data == old([data] + tailContents)[i];

	//end new
ensures delNd == old(delNd) && delNd != null;
//ensures delNd.footprint == old(delNd.footprint);
{
	
	curNd.next := curNd.next.next;

if (curNd.next == null)
{
	curNd.tailContents := [];
	curNd.footprint := {curNd};
	curNd.spine := [curNd];
}

else {
	curNd.tailContents := [curNd.next.data] + curNd.next.tailContents;
	curNd.footprint := {curNd} + curNd.next.footprint;
	curNd.spine := [curNd] + curNd.next.spine;
}
}

////////////////////////////////////////

//delete the range [start, end)
method deleteRange(start:int, end:int)  returns (delSet:set<INode>)
	requires 0 < start < end <= |tailContents| + 1;
	requires Valid();
	modifies footprint;
	ensures Valid();
	ensures [data] + tailContents == old(([data] + tailContents)[0..start] + ([data] + tailContents)[end..]);

	//new
	ensures footprint == old(footprint) - delSet;
{
	assert ValidLemma();
	assert |footprint| == |spine|;
	
	var rmNd := delete(start);

	//new
	delSet := {rmNd};
	//endNew
	
assert [data] + tailContents == old(([data] + tailContents)[0..start] + ([data] + tailContents)[start+1..]);

	if (start + 1 == end) {
assert  [data] + tailContents == old(([data] + tailContents)[0..start] + ([data] + tailContents)[end..]);
assert delSet == {rmNd};
	} else {
	 var delSet2	:= deleteRange(start, end - 1);

		delSet := delSet + delSet2;
	}
}

///////////////////////////////////////


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
//END of CLASS
}

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

predicate shrinkLemma(oldSpine:seq<INode>, pos: int, oldContents:seq<Data>)
  requires 0 <= pos < |oldSpine|;
	requires pos - 2 < |oldContents|;
	requires forall i :: 0 <= i <= pos-2 ==> oldSpine[i] != null && |oldSpine[i].tailContents| >= pos - i;
	requires forall i :: 0 <= i <= pos-2 ==> oldSpine[i].data == oldContents[i];
	reads oldSpine;
	ensures forall i :: 0 <= i <= pos-2 ==> (|oldSpine[0..pos-1][i].tailContents|) >= pos - i;
	ensures forall i :: 0 <= i <= pos-2 ==> oldSpine[0..pos-1][i].data == oldContents[i];
{
true
}	


ghost method updateSeq4Del(newSpine: seq<INode>, delNd:INode, pos: int, nxtNd:INode, oldContents:seq<Data>, thisNd:INode)
	requires listCond(newSpine);
	requires 1 < pos < |oldContents|;
requires |newSpine| == pos - 1;

requires nxtNd != null && nxtNd.Valid();
requires newSpine[|newSpine|-1].next == nxtNd;

//new
requires thisNd == newSpine[0];

requires delNd !in nxtNd.footprint && delNd !in newSpine;

requires (set nd | nd in newSpine) !! nxtNd.footprint;
requires newSpine[|newSpine|-1].footprint >= nxtNd.footprint;

//new
requires delNd != null;

requires newSpine[|newSpine|-1].tailContents == [nxtNd.data] + [delNd.data] + nxtNd.tailContents;

requires |newSpine[|newSpine|-1].tailContents| >= 2;

requires newSpine[|newSpine|-1].footprint == {newSpine[|newSpine|-1]} + nxtNd.footprint + {delNd};
	 
requires  forall i :: 0 <= i <= pos-2 ==> (|newSpine[i].tailContents|) >= pos - i;

requires |oldContents| > pos;
requires nxtNd.tailContents == oldContents[pos+1..];
requires nxtNd.data == oldContents[pos-1];
requires forall i :: 0 <= i <= pos-2 ==> newSpine[i].data == oldContents[i];
modifies newSpine;

ensures thisNd.Valid();
ensures  [thisNd.data] + thisNd.tailContents == oldContents[0..pos] + oldContents[pos+1..];

ensures thisNd.footprint == old(thisNd.footprint) - {delNd};

{

ghost var curIndex := pos - 2;

/////////pre to LI ok

while(curIndex >= 0)

	invariant -1 <= curIndex <= pos-2;

	invariant newSpine[|newSpine|-1].next == nxtNd;

	invariant nxtNd.Valid();

  invariant newSpine == old(newSpine);
	invariant thisNd == newSpine[0];

	invariant listInv(newSpine);


	invariant forall i :: 0 <= i <= curIndex ==> newSpine[i].tailContents == old(newSpine[i].tailContents) &&
		newSpine[i].footprint == old(newSpine[i].footprint) && newSpine[i].spine == old(newSpine[i].spine);

		//new
		invariant forall i :: 0 <= i < curIndex ==> newSpine[i].footprint == {newSpine[i]} + newSpine[i+1].footprint
			&&
			newSpine[i].tailContents == [newSpine[i+1].data] + newSpine[i+1].tailContents;
			
		invariant -1 <= curIndex < pos-2 ==> newSpine[curIndex+1].footprint == old(newSpine[curIndex+1].footprint - {delNd});
		
invariant forall nd :: nd in newSpine ==> nd.data == old(nd.data);
invariant nxtNd.data == old(nxtNd.data) && nxtNd.tailContents == old(nxtNd.tailContents);
invariant oldContents == old(oldContents);

invariant 0 <= curIndex <= pos-2 ==>  |newSpine[curIndex].tailContents| >= pos - curIndex;

//new
invariant -1 <= curIndex < pos - 2 ==>  [newSpine[curIndex+1].data] + newSpine[curIndex+1].tailContents == oldContents[curIndex+1..pos] + oldContents[pos+1..];	 
//end new
		
 invariant -1 <= curIndex < pos - 2 ==> newSpine[curIndex+1].Valid();
		
	modifies newSpine;
{
newSpine[curIndex].tailContents :=  [newSpine[curIndex].next.data] + newSpine[curIndex].next.tailContents;
newSpine[curIndex].footprint :=  {newSpine[curIndex]} + newSpine[curIndex].next.footprint;
newSpine[curIndex].spine :=  [newSpine[curIndex]] + newSpine[curIndex].next.spine;

curIndex := curIndex - 1;
}

assert curIndex == -1;

assert newSpine[curIndex+1].Valid();

assert [newSpine[curIndex+1].data] + newSpine[curIndex+1].tailContents == oldContents[curIndex+1..pos] + oldContents[pos+1..];

assert newSpine[curIndex+1].footprint == old(newSpine[curIndex+1].footprint - {delNd});

}


predicate validSeqTCLemma(mySeq: seq<INode>)
	requires validSeqCond(mySeq);
	reads mySeq, (set nd | nd in mySeq);

	ensures validSeqTCLemma(mySeq);
	ensures forall i :: 0 <= i < |mySeq| ==> |mySeq[i].tailContents| == |mySeq| - 1 - i;
{
if |mySeq| <= 1 then true
	else mySeq[0].tailContents == [mySeq[1].data] + mySeq[1].tailContents
		&& validSeqTCLemma(mySeq[1..])
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

&& (!exists nd :: nd !in head.footprint && nd in footprint)
&& contents == head.tailContents
&& head.footprint == spine
}


//////////////////////////////////
method contains(tarNd:INode) returns (isIn:bool)
	requires valid();
	requires tarNd != null && tarNd != head;
	modifies {};
	ensures valid();
	ensures isIn <==> tarNd in head.footprint - {head};
{
isIn := head.contains(tarNd);
}

method indexOf(tarNd:INode) returns (index:int)
	requires valid();
	requires tarNd != null && tarNd in head.footprint - {head};
	modifies {};

	ensures footprint == old(footprint);
	ensures valid();
	ensures 
		0 <= index < |head.spine| - 1
  && head.spine[index+1] == tarNd
	&& |contents| == |head.tailContents| == |head.spine| - 1
	&& tarNd.data == contents[index];

{
	index := head.indexOf(tarNd);

	assert index > 0;
	index := index - 1;
}


method delete(index:int)  returns (delNd:INode)
requires valid();
requires 0 <= index < |contents|;

modifies footprint;

ensures valid();
ensures contents == old(contents[0..index] + contents[index+1..]);
ensures footprint == old(footprint) - {delNd};

ensures 1 <= index + 1 < old(|head.spine|);
ensures delNd == old(head.spine[index+1]);
{
   delNd := head.delete(index+1);

   footprint := footprint - {delNd};

   spine := head.footprint;
   
   contents := head.tailContents;

assert head.ValidLemma() && head.ndValid2ListValidLemma();
}


method deleteRange(start:int, end:int) returns (delSet:set<INode>)
	requires valid();
	requires 0 <= start < end <= |contents|;
	modifies footprint;

  ensures valid();
	ensures contents == old(contents[0..start] + contents[end..]);
	ensures footprint == old(footprint) - delSet;
{
	delSet := head.deleteRange(start+1, end+1);

	footprint := footprint - delSet;
	spine := head.footprint;
	contents := head.tailContents;

	assert head.ValidLemma() && head.ndValid2ListValidLemma();
}


function method isIn(nd:INode, ndSet:set<INode>):bool
	ensures isIn(nd, ndSet) <==> nd in ndSet;
{
nd in ndSet
}

}

