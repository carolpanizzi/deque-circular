// Trabalho 2 - Métodos Formais
// Integrantes: Carolina Panizzi,

class DequeCircular {
  var a: array<int>
  var inicio: nat
  var quantidade: nat
  ghost var elementos: seq<int>
o
  ghost predicate Valid()
    reads this, a
  {
    a.Length > 0 &&
    0 <= inicio < a.Length &&
    0 <= quantidade <= a.Length &&
    |elementos| == quantidade &&
    (forall i: int :: 0 <= i < quantidade ==>
      a[(inicio + i) % a.Length] == elementos[i])
  }

  constructor(capacidade: int)
    requires capacidade > 0
    ensures Valid()
    ensures fresh(a)
    ensures a.Length == capacidade
    ensures inicio == 0
    ensures quantidade == 0
    ensures elementos == []
  {
    a := new int[capacidade];
    inicio := 0;
    quantidade := 0;
    elementos := [];
  }

  method Size() returns (tamanho: nat)
    requires Valid()
    ensures Valid()
    ensures tamanho == quantidade
    ensures tamanho == |elementos|
  {
    tamanho := quantidade;
  }

  method Capacity() returns (capacidade: nat)
    requires Valid()
    ensures Valid()
    ensures capacidade == a.Length
    ensures capacidade > 0
    ensures quantidade <= capacidade
  {
    capacidade := a.Length;
  }

  method IsEmpty() returns (vazio: bool)
    requires Valid()
    ensures Valid()
    ensures vazio <==> quantidade == 0
    ensures vazio <==> elementos == []
  {
    vazio := quantidade == 0;
  }

  method IsFull() returns (cheio: bool)
    requires Valid()
    ensures Valid()
    ensures cheio <==> quantidade == a.Length
    ensures cheio <==> |elementos| == a.Length
  {
    cheio := quantidade == a.Length;
  }
}

method ExemplosPessoa1()
{
  var deque := new DequeCircular(3);
  var tamanho := deque.Size();
  var capacidade := deque.Capacity();
  var vazio := deque.IsEmpty();
  var cheio := deque.IsFull();
  assert deque.Valid();
  assert deque.elementos == [];
  assert tamanho == 0;
  assert capacidade == 3;
  assert vazio && !cheio;

  var minimo := new DequeCircular(1);
  var tamanhoMinimo := minimo.Size();
  var capacidadeMinima := minimo.Capacity();
  var minimoVazio := minimo.IsEmpty();
  var minimoCheio := minimo.IsFull();
  assert tamanhoMinimo == 0 && capacidadeMinima == 1;
  assert minimoVazio && !minimoCheio;
  assert deque.Valid() && deque.elementos == [];
}
