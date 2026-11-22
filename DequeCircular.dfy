// Trabalho 2 - Métodos Formais - Turma 310
// Integrantes: Carolina Panizzi,Jullia Ross, Nathalie Jordão,Yasmin Weber

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

  // ===================== Pessoa 2 - Inserções =====================

  // Adiciona um novo elemento ao final do deque.
  // A posição física livre logo após o último elemento é
  // (inicio + quantidade) % a.Length; se passar do fim do array, volta ao índice 0.
  method PushBack(x: int)
    requires Valid()
    requires quantidade < a.Length          // o deque não pode estar cheio
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

    // Prova de que Valid() continua valendo:
    // os elementos antigos não foram sobrescritos e o novo está na última posição lógica.
    forall i | 0 <= i < quantidade
      ensures a[(inicio + i) % a.Length] == elementos[i]
    {
      if i < quantidade - 1 {
        ModDistinto(inicio, i, quantidade - 1, a.Length);
        assert a[(inicio + i) % a.Length] == old(a[(inicio + i) % a.Length]);
      }
    }
  }

  // Adiciona um novo elemento ao início do deque.
  // O início anda uma posição para trás; se estava em 0, volta para a última
  // posição do array (a.Length - 1), caracterizando a volta circular.
  method PushFront(x: int)
    requires Valid()
    requires quantidade < a.Length          // o deque não pode estar cheio
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

    // Prova de que Valid() continua valendo:
    // a posição lógica i (i >= 1) no novo deque corresponde à posição i-1 no antigo.
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
}

// ===================== Lemas auxiliares de aritmética modular =====================

// Para 0 <= x < 2n, o resto da divisão por n é x (se x < n) ou x - n (caso contrário).
lemma ModIntervalo(x: int, n: int)
  requires n > 0
  requires 0 <= x < 2 * n
  ensures x < n ==> x % n == x
  ensures x >= n ==> x % n == x - n
{
}

// Posições lógicas diferentes (menores que a capacidade) ocupam posições físicas
// diferentes no array circular. Garante que inserir não sobrescreve elementos.
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
  // Inserções simples no fim e no início, com volta circular do início (0 -> 2)
  var deque := new DequeCircular(3);
  deque.PushBack(10);
  assert deque.elementos == [10];
  deque.PushBack(20);
  assert deque.elementos == [10, 20];
  deque.PushFront(5);                    // inicio estava em 0: volta para a última posição
  assert deque.inicio == 2;
  assert deque.elementos == [5, 10, 20];
  var tamanho := deque.Size();
  var cheio := deque.IsFull();
  var vazio := deque.IsEmpty();
  assert tamanho == 3;
  assert cheio && !vazio;

  // Volta circular do fim: após PushFront o início fica em 2,
  // então os PushBack seguintes escrevem nas posições 0 e 1 do array
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

  // Somente PushFront: a ordem lógica fica invertida em relação à de inserção
  var frente := new DequeCircular(4);
  frente.PushFront(1);
  frente.PushFront(2);
  frente.PushFront(3);
  assert frente.elementos == [3, 2, 1];
  var tamanhoFrente := frente.Size();
  var frenteCheia := frente.IsFull();
  assert tamanhoFrente == 3 && !frenteCheia;

  // Capacidade mínima: uma inserção já enche o deque
  var minimo := new DequeCircular(1);
  minimo.PushFront(7);
  assert minimo.elementos == [7];
  var minimoCheio := minimo.IsFull();
  assert minimoCheio;

  // Os deques são independentes entre si
  assert deque.elementos == [5, 10, 20];
}
