/*Code Segment for Question 1*/ 

method Find(a: array<int>, v: int) returns (index: int)
    ensures index >= 0 ==> index < a.Length && a[index] == v
    ensures index < 0 ==> (forall k :: 0 <= k < a.Length ==> a[k] != v)
{
    var i: int := 0;
    while i < a.Length 
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> a[k] != v
    {
        if a[i] == v { return i; }
        i := i + 1;
    }
    return -1;
}

/*Code Segment Ends */

/*Code Segment for Question 2*/ 

method Sum(n: int) returns (sum: int)
    requires n > 0
    ensures sum == 5 * n * (n + 1)
{
    sum := 0;
    var i: int := n;
    while i > 0
        invariant sum == (n + i + 1) * (n - i) * 5
    {
        var k: int := 0;
        var j: int := i;
        while j > 0
            invariant k == (i - j) * 10
        {
            k := k + 10;
            j := j - 1;
        }
        sum := sum + k;
        i := i - 1;
    }
    return sum;
}

/*Code Segment Ends*/

/*Code Segment for Question 3 */

method ArrayMin(a: array<int>) returns (min: int)
    requires a.Length > 0
    ensures forall k :: 0 <= k < a.Length ==> a[k] >= min
    ensures exists k :: 0 <= k < a.Length && a[k] == min
{
    var i: int := 1;
    min := a[0];
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> a[k] >= min
        invariant exists k :: 0 <= k < i && a[k] == min
    {
        if a[i] < min {
            min := a[i];
        }
        i := i + 1;
    }
    return min;
}

/*Code Segment Ends */

/*Code Segment for Question 4 */

datatype CoinSide = Front | Back

predicate Before(a: CoinSide, b: CoinSide)
{
    a == Front || a==b
}

method SortCoins(a: array<CoinSide>)
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> Before(a[i],a[j])
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var f, b := 0, a.Length;
    while(f < b)
        invariant 0 <= f <= b <= a.Length
        invariant forall i :: 0 <= i < f ==> a[i] == Front
        invariant forall i :: b <= i < a.Length ==> a[i] == Back
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        match a[f]
        case Front =>
            f := f + 1;
        case Back =>
            b := b - 1;
            a[f], a[b] := a[b], a[f];  
    }
}

method Main()
{
    var coins:= new CoinSide[10][Back,Front,Back,Front,Back,Front,Back,Front,Back,Front];
    SortCoins(coins);
    for i: int := 0 to 10
    {
        if coins[i] == Front{
            print("Front ");
        }
        else{
            print("Back ");
        }
    }
    print("\n");
}

/*Code Segment Ends */