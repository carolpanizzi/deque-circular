// Trabalho 2 - Métodos Formais - Turma 310
// Integrantes: Carolina Panizzi, Nathalie Jordão, Yasmin Weber

class DequeCircular {
  var a: array<int>
  var inicio: nat
  var quantidade: nat
  ghost var elementos: seq<int>

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

  // posicao fisica livre depois do ultimo elemento = (inicio + quantidade) % a.length
  // se passar do fim do array, volta ao indice 0
  method PushBack(x: int)
    requires Valid()
    requires quantidade < a.Length          // o deque nao pode estar cheio
    modifies this, a
    ensures Valid()
    ensures a == old(a)                     // o array continua o mesmo (mesma capacidade)
    ensures a.Length == old(a.Length)
    ensures inicio == old(inicio)
    ensures quantidade == old(quantidade) + 1
    ensures elementos == old(elementos) + [x]
  {
    var pos := (inicio + quantidade) % a.Length;
    a[pos] := x;
    elementos := elementos + [x];
    quantidade := quantidade + 1;

    // valid() continua valendo: os elem. antigos nao foram sobrescritos e o novo esta na ultima posicao logica
    forall i | 0 <= i < quantidade
      ensures a[(inicio + i) % a.Length] == elementos[i]
    {
      if i < quantidade - 1 {
        ModDistinto(inicio, i, quantidade - 1, a.Length);
        assert a[(inicio + i) % a.Length] == old(a[(inicio + i) % a.Length]);
      }
    }
  }

  // adiciona um novo elemento ao inicio do deque
  // o inicio anda uma posicao para tras; se estava em 0, volta para a ultima posicao
  method PushFront(x: int)
    requires Valid()
    requires quantidade < a.Length          // o deque nao pode estar cheio
    modifies this, a
    ensures Valid()
    ensures a == old(a)
    ensures a.Length == old(a.Length)
    ensures inicio == (if old(inicio) == 0 then a.Length - 1 else old(inicio) - 1)
    ensures quantidade == old(quantidade) + 1
    ensures elementos == [x] + old(elementos)
  {
    var novoInicio := if inicio == 0 then a.Length - 1 else inicio - 1;
    a[novoInicio] := x;
    inicio := novoInicio;
    elementos := [x] + elementos;
    quantidade := quantidade + 1;

    // prova de que valid() continua valendo
    // a posicao logica i (i >= 1) no novo deque corresponde a posicao i-1 no antigo
    forall i | 0 <= i < quantidade
      ensures a[(inicio + i) % a.Length] == elementos[i]
    {
      ModIntervalo(inicio, a.Length);
      if i > 0 {
        ModIntervalo(inicio + i, a.Length);
        ModIntervalo(old(inicio) + (i - 1), a.Length);
        assert (inicio + i) % a.Length == (old(inicio) + (i - 1)) % a.Length;
        ModDistinto(inicio, 0, i, a.Length);
        assert a[(inicio + i) % a.Length] == old(a[(inicio + (i - 1)) % a.Length]);
        assert elementos[i] == old(elementos)[i - 1];
      }
    }
  }

  // remove e retorna o primeiro elemento do deque
  method PopFront() returns (valor: int)
    requires Valid()
    requires quantidade > 0
    modifies this
    ensures Valid()
    ensures a == old(a)
    ensures a.Length == old(a.Length)
    ensures inicio == (old(inicio) + 1) % a.Length
    ensures quantidade == old(quantidade) - 1
    ensures valor == old(elementos[0])
    ensures elementos == old(elementos)[1..]
  {
    valor := a[inicio];
    inicio := (inicio + 1) % a.Length;
    quantidade := quantidade - 1;
    elementos := elementos[1..];

    // cada elemento restante passa a ocupar a posicao logica anterior
    forall i | 0 <= i < quantidade
      ensures a[(inicio + i) % a.Length] == elementos[i]
    {
      assert 0 <= i + 1 < old(quantidade);
      assert elementos[i] == old(elementos)[i + 1];
      // inicio == old(inicio) + 1, ou 0 se old(inicio) era a ultima posicao (volta circular)
      ModIntervalo(old(inicio) + 1, a.Length);
      ModIntervalo(inicio + i, a.Length);
      ModIntervalo(old(inicio) + i + 1, a.Length);
      assert (inicio + i) % a.Length ==
             (old(inicio) + i + 1) % a.Length;
      // dentro de old(...), "inicio" ja se refere ao valor antigo
      assert a[(old(inicio) + i + 1) % a.Length] ==
             old(a[(inicio + i + 1) % a.Length]);
      assert old(a[(inicio + i + 1) % a.Length]) ==
             old(elementos)[i + 1];
    }
  }

  // remove e retorna o ultimo elemento do deque
  method PopBack() returns (valor: int)
    requires Valid()
    requires quantidade > 0
    modifies this
    ensures Valid()
    ensures a == old(a)
    ensures a.Length == old(a.Length)
    ensures inicio == old(inicio)
    ensures quantidade == old(quantidade) - 1
    ensures valor == old(elementos[|elementos| - 1])
    ensures elementos == old(elementos)[..|old(elementos)| - 1]
  {
    valor := a[(inicio + quantidade - 1) % a.Length];
    quantidade := quantidade - 1;
    elementos := elementos[..|elementos| - 1];

    // os elementos restantes mantem suas posicoes fisicas e sua ordem logica
    forall i | 0 <= i < quantidade
      ensures a[(inicio + i) % a.Length] == elementos[i]
    {
      assert 0 <= i < old(quantidade);
      assert elementos[i] == old(elementos)[i];
      // dentro de old(...), "inicio" ja se refere ao valor antigo
      assert a[(inicio + i) % a.Length] ==
             old(a[(inicio + i) % a.Length]);
      assert old(a[(inicio + i) % a.Length]) ==
             old(elementos)[i];
    }
  }

  // verifica se x pertence ao deque
  // percorre as posicoes logicas 0..quantidade-1 no array circular
  method Contains(x: int) returns (pertence: bool)
    requires Valid()
    ensures Valid()
    ensures pertence <==> x in elementos
  {
    var i := 0;
    while i < quantidade
      invariant 0 <= i <= quantidade
      invariant forall k :: 0 <= k < i ==> elementos[k] != x   // nada encontrado ate i
      decreases quantidade - i
    {
      if a[(inicio + i) % a.Length] == x {
        assert elementos[i] == x;
        pertence := true;
        return;
      }
      i := i + 1;
    }
    pertence := false;
  }

  // redimensiona o deque para uma capacidade maior
  // como arrays tem tamanho fixo, aloca um array novo e copia os elementos
  // na ordem logica (desfazendo a volta circular): o primeiro vai para a posicao 0
  method Resize(novaCapacidade: int)
    requires Valid()
    requires novaCapacidade > a.Length      // so permite crescer
    modifies this
    ensures Valid()
    ensures fresh(a)
    ensures a.Length == novaCapacidade
    ensures inicio == 0
    ensures quantidade == old(quantidade)
    ensures elementos == old(elementos)     // o conteudo e a ordem nao mudam
  {
    var novo := new int[novaCapacidade];
    var i := 0;
    while i < quantidade
      invariant 0 <= i <= quantidade
      invariant Valid()
      invariant novo.Length == novaCapacidade
      invariant forall k :: 0 <= k < i ==> novo[k] == elementos[k]
      modifies novo
      decreases quantidade - i
    {
      novo[i] := a[(inicio + i) % a.Length];
      i := i + 1;
    }
    a := novo;
    inicio := 0;

    // prova de que valid() vale no array novo: com inicio == 0 e
    // k < quantidade < a.length, a posicao fisica (0 + k) % a.length e o proprio k
    forall k | 0 <= k < quantidade
      ensures a[(inicio + k) % a.Length] == elementos[k]
    {
      ModIntervalo(inicio + k, a.Length);
    }
  }
}

// para 0 <= x < 2n, o resto da divisao por n e x (se x < n) ou x - n (caso contrario)
lemma ModIntervalo(x: int, n: int)
  requires n > 0
  requires 0 <= x < 2 * n
  ensures x < n ==> x % n == x
  ensures x >= n ==> x % n == x - n
{
}

// posicoes logicas diferentes (menores que a capacidade) ocupam posicoes fisicas
// diferentes no array circular. garante que inserir nao sobrescreve elementos
lemma ModDistinto(inicio: int, i: int, j: int, n: int)
  requires n > 0
  requires 0 <= inicio < n
  requires 0 <= i < j < n
  ensures (inicio + i) % n != (inicio + j) % n
{
  ModIntervalo(inicio + i, n);
  ModIntervalo(inicio + j, n);
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

method ExemplosPessoa2()
{
  // insercoes simples no fim e no inicio, com volta circular do inicio (0 -> 2)
  var deque := new DequeCircular(3);
  deque.PushBack(10);
  assert deque.elementos == [10];
  deque.PushBack(20);
  assert deque.elementos == [10, 20];
  deque.PushFront(5);                    // inicio estava em 0: volta para a ultima posicao
  assert deque.inicio == 2;
  assert deque.elementos == [5, 10, 20];
  var tamanho := deque.Size();
  var cheio := deque.IsFull();
  var vazio := deque.IsEmpty();
  assert tamanho == 3;
  assert cheio && !vazio;

  // volta circular do fim: apos pushfront o inicio fica em 2,
  // entao os pushback seguintes escrevem nas posicoes 0 e 1 do array
  var circular := new DequeCircular(3);
  circular.PushFront(1);
  assert circular.inicio == 2;
  circular.PushBack(2);
  circular.PushBack(3);
  assert circular.elementos == [1, 2, 3];
  var circularCheio := circular.IsFull();
  assert circularCheio;
  var capacidade := circular.Capacity();
  assert capacidade == 3;

  // somente pushfront: a ordem logica fica invertida em relacao a de insercao
  var frente := new DequeCircular(4);
  frente.PushFront(1);
  frente.PushFront(2);
  frente.PushFront(3);
  assert frente.elementos == [3, 2, 1];
  var tamanhoFrente := frente.Size();
  var frenteCheia := frente.IsFull();
  assert tamanhoFrente == 3 && !frenteCheia;

  // capacidade minima: uma insercao ja enche o deque
  var minimo := new DequeCircular(1);
  minimo.PushFront(7);
  assert minimo.elementos == [7];
  var minimoCheio := minimo.IsFull();
  assert minimoCheio;

  // os deques sao independentes entre si
  assert deque.elementos == [5, 10, 20];
}

method Main()
{
  // criacao do deque
  var deque := new DequeCircular(3);
  var tamanho := deque.Size();
  var capacidade := deque.Capacity();
  var vazio := deque.IsEmpty();
  var cheio := deque.IsFull();
  assert tamanho == 0 && capacidade == 3;
  assert vazio && !cheio;

  var tem := deque.Contains(1);
  assert !tem;

  deque.PushBack(2);                     // [2]
  deque.PushFront(1);                    // [1, 2]
  deque.PushBack(3);                     // [1, 2, 3]
  assert deque.elementos == [1, 2, 3];
  cheio := deque.IsFull();
  assert cheio;

  // busca de elemento presente e ausente
  tem := deque.Contains(2);
  assert tem;
  tem := deque.Contains(9);
  assert !tem;

  // remocoes nas duas pontas: valores retornados e ordem restante
  var primeiro := deque.PopFront();
  assert primeiro == 1;
  assert deque.elementos == [2, 3];
  var ultimo := deque.PopBack();
  assert ultimo == 3;
  assert deque.elementos == [2];
  print "Removidos: ", primeiro, " e ", ultimo, "\n";

  // nova volta circular depois das remocoes; deque cheio de novo
  deque.PushFront(7);                    // [7, 2]
  deque.PushBack(8);                     // [7, 2, 8]
  assert deque.elementos == [7, 2, 8];
  cheio := deque.IsFull();
  assert cheio;
  tem := deque.Contains(3);              // o 3 foi removido antes
  assert !tem;

  // redimensionamento com o deque cheio: dados e ordem preservados
  deque.Resize(6);
  assert deque.elementos == [7, 2, 8];
  capacidade := deque.Capacity();
  tamanho := deque.Size();
  cheio := deque.IsFull();
  assert capacidade == 6 && tamanho == 3;
  assert !cheio;
  print "Nova capacidade: ", capacidade, "\n";

  // insercoes depois de crescer (pushfront volta para a ultima posicao do array novo)
  deque.PushFront(0);                    // [0, 7, 2, 8]
  deque.PushBack(9);                     // [0, 7, 2, 8, 9]
  assert deque.elementos == [0, 7, 2, 8, 9];
  tem := deque.Contains(9);
  assert tem;

  // esvaziar o deque alternando as pontas
  var r1 := deque.PopFront();
  var r2 := deque.PopBack();
  var r3 := deque.PopFront();
  var r4 := deque.PopBack();
  var r5 := deque.PopFront();
  assert r1 == 0 && r2 == 9 && r3 == 7 && r4 == 8 && r5 == 2;
  vazio := deque.IsEmpty();
  assert vazio;
  tem := deque.Contains(2);
  assert !tem;
  print "Deque vazio no final: ", vazio, "\n";
}