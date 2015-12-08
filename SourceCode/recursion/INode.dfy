class Data {}
class INode 
{
ghost var tailContents: seq<Data>;
ghost var footprint: set<INode>;

var data: Data;
var next: INode;

predicate good()
reads this, footprint;
{
    this in footprint 
	&& (next != null ==> (next in footprint 
	&& this !in next.footprint 
	&& footprint == {this} + next.footprint
	&& tailContents == [next.data] + next.tailContents
	))
	&& (next ==null ==> tailContents == [] && footprint == {this})
}

predicate Valid()
reads this, footprint;
{
    good() && (next != null ==> next.Valid())
}


predicate lenLemma()
requires Valid();
reads this, footprint;
ensures lenLemma();
ensures |footprint| == |tailContents| + 1;
{
if (next == null) then footprint == {this}
						&& tailContents == []
else footprint == {this} + next.footprint &&
	 tailContents == [next.data] + next.tailContents
		&& next.lenLemma()
}


predicate ValidLemma()
requires Valid();
reads this, footprint;
ensures ValidLemma();
ensures forall nd :: nd in footprint ==> nd != null && nd.footprint <= footprint;
{
if next == null then (footprint == {this})
else (
footprint == {this} + next.footprint
&& next.ValidLemma())
}


predicate allVLemma()
requires Valid();
reads this, footprint;
ensures allVLemma();
ensures |tailContents| == |footprint|-1;
ensures forall nd :: nd in footprint ==> nd != null && nd.Valid();
{
next != null ==> next.allVLemma()
}



constructor init(d:Data) 
modifies this;
ensures Valid();
ensures data == d;
ensures next == null;

ensures footprint == {this};
ensures tailContents == [];
ensures fresh(footprint - {this});
{
    data := d;
	next := null;
    tailContents := [];
	footprint := {this};
}



method preAppend(d:Data) returns (node:INode)
requires Valid();
ensures node != null && node.Valid();
ensures node.data == d && node.next == this;
ensures node.tailContents == [this.data] + this.tailContents;
{
var r := new INode.init(d);
r.next := this;

r.footprint := r.footprint + this.footprint;
r.tailContents := [this.data] + this.tailContents;
return r;
}

method append(d:Data) returns (newNd:INode)
requires Valid();

modifies footprint;
decreases footprint;
ensures Valid();
ensures (tailContents == old(tailContents) + [d]);
ensures this.data == old(this.data);
ensures footprint == old(footprint) + {newNd};
ensures fresh(newNd);
{

if(next == null)
{
newNd := new INode.init(d);
next := newNd;
this.tailContents := [d];
}

else
 {
newNd := next.append(d);
this.tailContents := [this.next.data] + this.next.tailContents;
}

this.footprint := {this} + next.footprint;

}


method insertAt(i:int, d:Data) returns (newNd: INode)
requires 0 < i <= |tailContents|;
requires Valid();
modifies footprint;
ensures Valid();
ensures this.data == old(this.data);
ensures tailContents == old(tailContents[0..i-1]) + [d] + old(tailContents[i-1..]);
ensures footprint == old(footprint) + {newNd};
ensures fresh(newNd);
{
newNd := new INode.init(d);

if (i == 1) {
newNd.next := next;
newNd.tailContents := tailContents;
newNd.footprint := {newNd} + next.footprint;

assert newNd.tailContents == old(tailContents[i-1..]);
assert newNd.Valid();

this.next := newNd;
}

else {
newNd := next.insertAt(i-1, d);
}

this.tailContents := [next.data] + next.tailContents;

assert tailContents == old(tailContents[0..i-1]) + [d] + old(tailContents[i-1..]);

this.footprint := {this} + next.footprint;
}

////////////////////////////////////////////////////////

method update(d:Data, index:int)
requires 0 <= index <= |tailContents|;
requires Valid();
modifies footprint;
ensures Valid();
ensures index == 0 ==> (data == d && tailContents == old(tailContents));
ensures index > 0 ==> (this.data == old(this.data)
&& tailContents == old(tailContents[0..index-1]) + [d] +
						old(tailContents[index..]));
ensures footprint == old(footprint);
{
if (index == 0) {data := d; }
else {
next.update(d, index-1);
tailContents := [next.data] + next.tailContents;
}
}


method get(index:int) returns (d:Data)
requires Valid();
requires 0 <= index <= |tailContents|;

ensures Valid();
ensures d == (if index == 0 then data else tailContents[index-1]);
{
if index == 0 {return data;} 
else {d := next.get(index-1);}
}



method delete(index:int) returns (delNd:INode)
requires Valid();
requires 0 < index <= |tailContents|;

modifies footprint;
ensures Valid();

ensures delNd in old(footprint);
ensures data == old(data);
ensures tailContents == old(tailContents[0..index-1]) + old(tailContents[index..]);
ensures footprint == old(footprint) - {delNd};
{
if (index == 1) {
    delNd := next;
    next := next.next;
    
    footprint := footprint - {delNd};
    tailContents := if next == null then [] else 
			[next.data] + next.tailContents;
}

else {
    delNd := next.delete(index-1);
    
    footprint := footprint - {delNd};
    tailContents := [next.data] + next.tailContents;
}

}

}

function getFtprint(nd:INode): set<INode>
reads nd;
{
if nd == null then {} else nd.footprint
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


method init()
modifies this;
ensures valid() && fresh(footprint - {this});
ensures |contents| == 0;
ensures spine == {head};
ensures head.next == null;
{
head := new INode.init(null);

contents := head.tailContents;

footprint := {this};
footprint := footprint + head.footprint;
spine := {head};
}


method len() returns (len:int)
requires valid();
ensures valid();
ensures len == |contents|;
{
var tmp:INode;
tmp := head;
len := 0;

while(tmp.next != null)
decreases tmp.footprint;
invariant tmp != null && tmp.Valid();
invariant tmp.next == null ==> tmp.tailContents == [];
invariant len + |tmp.tailContents| == |contents|;
{
len := len + 1;

tmp := tmp.next;
}

}

method get(index:int) returns (d:Data)
requires valid();
requires 0 <= index < |contents|;

ensures valid();
ensures d == contents[index];
{
d := head.get(index+1);
}


method add2Front(d:Data)
modifies footprint;
requires valid();
requires d != null;

ensures valid();
ensures contents == [d] + old(contents);
ensures fresh(footprint - old(footprint));
{
head.data := d;

var newHead := new INode.init(null);
newHead.next := head;

newHead.footprint := {newHead} + head.footprint;
newHead.tailContents := [d] + head.tailContents;

head := newHead;

footprint := footprint + {newHead};

spine := spine + {head};

contents := head.tailContents;

assert head.allVLemma();
}

method append(d:Data)
requires valid();

modifies footprint;
ensures valid();
ensures (contents == old(contents) + [d]);
ensures fresh(footprint - old(footprint));
{
var newNd := head.append(d);

footprint := footprint + {newNd};
spine := spine + {newNd};
contents := head.tailContents;

assert head.allVLemma() && head.ValidLemma();

}


method insertAt(i:int, d:Data)
requires 0 < i < |contents|;
requires valid();
modifies footprint;
ensures valid();
ensures contents == old(contents[0..i]) + [d] + old(contents[i..]);
ensures fresh(footprint - old(footprint));
{
var newNd := head.insertAt(i+1, d);

footprint := footprint + {newNd};
spine := spine + {newNd};
contents := head.tailContents;

assert head.allVLemma() && head.ValidLemma();
}


method insert(d:Data, pos:int) 
modifies footprint;
requires valid();
requires d != null;
requires 0 <= pos <= |contents|;

ensures valid();
ensures |contents| == (|old(contents)| + 1);

ensures pos == 0 ==> contents == [d] + old(contents);
ensures pos == |contents| ==> contents == old(contents) + [d];
ensures 0 < pos < |contents| ==> contents == 
		old(contents[0..pos]) + [d] + old(contents[pos..]);

ensures fresh(footprint - old(footprint));
{

var length := this.len();
if (pos == 0) {
add2Front(d);
}

else if (pos == length) {
append(d);
}

else {
insertAt(pos, d);
}
}


method update(d:Data, index:int)
requires 0 <= index < |contents|;
requires valid();
modifies footprint;
ensures valid();
ensures contents == old(contents[0..index]) + [d] + old(contents[index+1..]);
ensures footprint == old(footprint);
{
head.update(d, index+1);

contents := head.tailContents;

assert head.allVLemma() && head.ValidLemma();
}


method delete(index:int)  returns (delNd:INode)
requires valid();
requires 0 <= index < |contents|;

modifies footprint;
ensures valid();
ensures contents == old(contents[0..index]) + old(contents[index+1..]);
ensures footprint == old(footprint) - {delNd};
ensures spine == old(spine) - {delNd};
{
   delNd := head.delete(index+1);

   footprint := footprint - {delNd};

   spine := head.footprint;
   
   contents := head.tailContents;

   assert head.allVLemma() && head.ValidLemma();
}


}


