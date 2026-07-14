// ------------------------------------------------------
//  T2 - Métodos Formais para Computação
//
//  Augusto Baldino, Bianca Alves e Carolina Brose
// ------------------------------------------------------


method Main() {
  // Cria um deque circular com capacidade inicial de 5
  var deque := new CircularDeque(5);

  var empty := deque.IsEmpty();
  assert empty;

  deque.PushTail(1);
  // Verifica exatamente onde o "1" está armazenado
  assert deque.elements[deque.tail] == 1;
  ghost var t1 := deque.tail;

  deque.PushTail(2);
  // Verifica onde o "2" está armazenado e que o "1" permaneceu após a condição de frame
  assert deque.elements[deque.tail] == 2;
  assert deque.elements[t1] == 1;
  ghost var t2 := deque.tail;

  deque.PushHead(0);
  // Verifica onde o "0" está armazenado e que "1" e "2" permaneceram
  assert deque.elements[deque.head] == 0;
  assert deque.elements[t1] == 1;
  assert deque.elements[t2] == 2;

  var size := deque.Size();
  assert size == 3;

  // Explicita as testemunhas que Contains() precisa, usando Index(k), para que os
  // quantificadores existenciais/universais na pós-condição de Contains tenham
  // termos concretos para comparação.
  assert deque.elements[deque.Index(0)] == 0;
  assert deque.elements[deque.Index(1)] == 1;
  assert deque.elements[deque.Index(2)] == 2;

  var contains1 := deque.Contains(1);
  if !contains1 {
    // O ensures de Contains fornece: forall k :: 0<=k<size ==> elements[Index(k)] != 1
    // Instancia explicitamente em k=1 em vez de depender da inferência automática;
    // isso contradiz diretamente o assert de verificação acima.
    assert deque.elements[deque.Index(1)] != 1;
    assert false;
  }
  assert contains1;

  var contains3 := deque.Contains(3);
  if contains3 {
    // O ensures de Contains fornece: exists k :: 0<=k<size && elements[Index(k)] == 3
    // Extrai a testemunha explicitamente e separa os casos dos únicos valores possíveis.
    ghost var k :| 0 <= k < size && deque.elements[deque.Index(k)] == 3;
    assert k == 0 || k == 1 || k == 2;
    assert false;
  }
  assert !contains3;

  var head := deque.PopHead();
  assert head == 0;

  var tail := deque.PopTail();
  assert tail == 2;

  // Altera a capacidade do deque para 10
  deque.SetCapacity(10);
  var cap := deque.Capacity();
  assert cap == 10;
}



class CircularDeque {
  // Estados internos do deque
  var capacity: int
  var size: int
  var head: int
  var tail: int
  var elements: array<int>

  // > Predicados
  ghost predicate Valid() reads this, elements {
    capacity > 0 &&                   // A capacidade deve ser um inteiro positivo
    size >= 0 &&                      // O tamanho atual do deque é um inteiro não negativo
    size <= capacity &&               // O tamanho atual do deque não excede a capacidade
    head >= 0 &&                      // O índice do primeiro elemento é inteiro não negativo
    head < capacity &&                // O índice do primeiro elemento não excede a capacidade
    tail >= -1 &&                     // O índice do último elemento é inteiro não negativo ou -1 (indicando deque vazio)
    tail < capacity &&                // O índice do último elemento não excede a capacidade
    (size > 0 ==> tail == (head + size - 1) % capacity) &&  // Se o deque não está vazio, o índice do último elemento é calculado corretamente a partir do índice do primeiro elemento e do tamanho
    elements.Length == capacity                             // O array de elementos tem o tamanho igual a capacidade (array estático)
  }

  // > Funções auxiliares
  function Index(k: int): int
    reads this                          // Indica que a função lê o estado do objeto (this) para fins de verificação formal
    requires capacity > 0               // Pré-condição: A capacidade deve ser um inteiro positivo
  {
    (head + k) % capacity
  }

  constructor(capacity: int)
    requires capacity > 0               // Pré-condição: A capacidade deve ser um inteiro positivo
    ensures Valid()                     // Pós-condição: O deque deve ser válido após a construção
    ensures this.capacity == capacity   // Pós-condição: A capacidade do deque é igual à capacidade fornecida
    ensures size == 0                   // Pós-condição: O tamanho do deque é inicializado como zero (sem elementos)
    ensures head == 0                   // Pós-condição: O índice do primeiro elemento é inicializado como zero
    ensures tail == -1                  // Pós-condição: O índice do último elemento é inicializado como -1 (indicando que não há elementos)
    ensures fresh(elements)             // Pós-condição: O array de elementos é alocado dinamicamente (fresh) e tem o tamanho igual à capacidade
  {
    this.capacity := capacity;
    this.size := 0;
    this.head := 0;
    this.tail := -1;
    this.elements := new int[capacity];
  }


  // --------------- MÉTODOS --------------------

  // > Métodos de consulta
  method IsEmpty() returns (empty: bool)
    requires Valid()                    // Pré-condição: O deque deve ser válido
    ensures empty == (size == 0)        // Pós-condição: empty é verdadeiro se o tamanho atual do deque for zero (sem elementos)
  {
    empty := (size == 0);
  }

  method IsFull() returns (full: bool)
    requires Valid()                    // Pré-condição: O deque deve ser válido
    ensures full == (size == capacity)  // Pós-condição: full é verdadeiro se o tamanho atual do deque for igual à sua capacidade
  {
    full := (size == capacity);
  }

  method Size() returns (currentSize: int)
    requires Valid()                    // Pré-condição: O deque deve ser válido
    ensures currentSize == size         // Pós-condição: currentSize é igual ao tamanho atual do deque
  {
    currentSize := size;
  }

  method Capacity() returns (maxCapacity: int)
    requires Valid()                    // Pré-condição: O deque deve ser válido
    ensures maxCapacity == capacity     // Pós-condição: maxCapacity é igual à capacidade atual do deque
  {
    maxCapacity := capacity;
  }

  method Contains(value: int) returns (found: bool)
    requires Valid()                    // Pré-condição: O deque deve ser válido
    requires size > 0                   // Pré-condição: O deque não pode estar vazio (deve haver elementos)
    ensures Valid()                     // Pós-condição: O deque continua válido após a execução
    ensures found ==>  
      exists k {:trigger elements[Index(k)]} ::
      0 <= k < size && elements[Index(k)] == value // Pós-condição: Se achou (found == true), garante que existe um índice k tal que o elemento no índice k é igual ao valor procurado
    ensures !found ==> 
      forall k {:trigger elements[Index(k)]} ::
      0 <= k < size ==> elements[Index(k)] != value // Pós-condição: Se não achou (found == false), garante que nenhum elemento no deque é igual ao valor procurado
  {
    var i := 0;

    while i < size
      invariant Valid()                  // Garante que o deque continua válido durante a busca
      invariant 0 <= i <= size           // Garante que 'i' está sempre dentro dos limites do tamanho atual do deque
      invariant forall k {:trigger elements[Index(k)]} ::
      0 <= k < i ==>
      elements[Index(k)] != value        // Garante que nenhum dos elementos já verificados é igual ao valor procurado
      decreases size - i                 // Garante que o loop progride em direção à condição de parada
    {
      if elements[Index(i)] == value {
        return true;
      }

      i := i + 1;
    }

    return false;
  }

  // > Métodos de modificação
  method PushHead(value: int)
    modifies this, this.elements
    requires Valid()                        // Pré-condição: O deque deve ser válido
    requires size < capacity                // Pré-condição: O deque não pode estar cheio (tamanho atual menor que a capacidade)
    ensures Valid()                         // Pós-condição: O deque continua válido após a execução
    ensures size == old(size) + 1           // Pós-condição: O tamanho atual do deque é igual ao tamanho antigo mais 1
    ensures size <= capacity                // Pós-condição: O tamanho atual do deque é menor ou igual à capacidade
    ensures capacity == old(capacity)       // Pós-condição: A capacidade do deque permanece a mesma após a execução
    ensures elements == old(elements)       // Pós-condição: O array de elementos permanece o mesmo após a execução (exceto pelo novo elemento inserido)
    ensures elements[head] == value         // Pós-condição: O elemento na cabeça do deque é igual ao valor inserido
    ensures head == (old(head) - 1 + capacity) % capacity  // Pós-condição: fórmula exata da nova cabeça, para permitir que chamadores calculem índices concretamente
    ensures forall i {:trigger elements[i]} ::
      0 <= i < capacity && i != head ==>
      elements[i] == old(elements[i])       // Pós-condição: Todos os elementos do deque, exceto o novo elemento na cabeça, permanecem inalterados
    ensures old(size) == 0 ==> tail == head // Pós-condição: Se o deque estava vazio, tail e head apontam para o mesmo (único) elemento
  {
    if size == capacity {
      return;
    }

    var oldHead := head;
    head := (head - 1 + capacity) % capacity;
    elements[head] := value;

    if size == 0 {
      tail := head;  // deque estava vazio: tail deve apontar para o mesmo elemento que head
    } else {
      // Ajuda o verificador com a aritmética modular de wrap-around exigida
      // por Valid() (tail == (head + size - 1) % capacity), separando o
      // caso "sem wrap" do caso "com wrap" em vez de deixar uma única
      // identidade não-linear para o Z3 resolver de uma vez.
      if oldHead > 0 {
        assert head == oldHead - 1;
      } else {
        assert oldHead == 0;
        assert head == capacity - 1;
      }
    }
    size := size + 1;
  }

  method PushTail(value: int)
    modifies this, this.elements 
    requires Valid()                        // Pré-condição: O deque deve ser válido
    requires size < capacity                // Pré-condição: O deque não pode estar cheio (tamanho atual menor que a capacidade)
    ensures Valid()                         // Pós-condição: O deque continua válido após a execução
    ensures size == old(size) + 1           // Pós-condição: O tamanho atual do deque é igual ao tamanho antigo mais 1
    ensures size <= capacity                // Pós-condição: O tamanho atual do deque é menor ou igual à capacidade
    ensures capacity == old(capacity)       // Pós-condição: A capacidade do deque permanece a mesma após a execução
    ensures elements == old(elements)       // Pós-condição: O array de elementos permanece o mesmo após a execução (exceto pelo novo elemento inserido)
    ensures elements[tail] == value         // Pós-condição: O elemento na cauda do deque é igual ao valor inserido
    ensures tail == (old(tail) + 1) % capacity  // Pós-condição: fórmula exata da nova cauda
    ensures forall i {:trigger elements[i]} :: 
      0 <= i < capacity && i != tail ==>
      elements[i] == old(elements[i])       // Pós-condição: Todos os elementos do deque, exceto o novo elemento na cauda, permanecem inalterados
    ensures old(size) == 0 ==> tail == head // Pós-condição: Se o deque estava vazio, tail e head apontam para o mesmo (único) elemento
  {
    if size == capacity {
      return;
    }

    var oldTail := tail;
    tail := (tail + 1) % capacity;
    elements[tail] := value;

    if size == 0 {
      head := tail;  // deque estava vazio: head deve apontar para o mesmo elemento que tail
    } else {
      // Mesmo truque do PushHead: separa o caso de wrap-around explicitamente.
      if oldTail < capacity - 1 {
        assert tail == oldTail + 1;
      } else {
        assert oldTail == capacity - 1;
        assert tail == 0;
      }
    }
    size := size + 1;
  }

  method PopHead() returns (value: int)
    modifies this
    requires Valid()                        // Pré-condição: O deque deve ser válido
    requires size > 0                       // Pré-condição: O deque não pode estar vazio (deve haver elementos)
    ensures Valid()                         // Pós-condição: O deque continua válido após a execução
    ensures size == old(size) - 1           // Pós-condição: O tamanho atual do deque é igual ao tamanho antigo menos 1
    ensures capacity == old(capacity)       // Pós-condição: A capacidade do deque permanece a mesma após a execução
    ensures elements == old(elements)       // Pós-condição: O array de elementos permanece o mesmo após a execução (exceto pelo elemento removido)
    ensures value == old(elements[head])    // Pós-condição: value é igual ao elemento que estava na cabeça do deque antes da execução
    ensures head == (old(head) + 1) % capacity  // Pós-condição: fórmula exata da nova cabeça (o corpo sempre a atualiza assim, mesmo quando o deque esvazia)
    ensures forall i {:trigger elements[i]} ::
      0 <= i < capacity && i != head ==>
      elements[i] == old(elements[i])       // Pós-condição: Todos os elementos do deque, exceto o novo elemento na cabeça, permanecem inalterados
    ensures old(size) == 1 ==> tail == -1   // Pós-condição: Se o deque tinha apenas um elemento, tail é resetado para -1 (indicando que o deque está vazio)
  {
    value := elements[head];
    head := (head + 1) % capacity;
    if size == 1 {
      tail := -1; // deque ficará vazio: tail deve ser resetado para -1
    }
    size := size - 1;
  }

  method PopTail() returns (value: int)
    modifies this
    requires Valid()                        // Pré-condição: O deque deve ser válido
    requires size > 0                       // Pré-condição: O deque não pode estar vazio (deve haver elementos)
    ensures Valid()                         // Pós-condição: O deque continua válido após a execução
    ensures size == old(size) - 1           // Pós-condição: O tamanho atual do deque é igual ao tamanho antigo menos 1
    ensures capacity == old(capacity)       // Pós-condição: A capacidade do deque permanece a mesma após a execução
    ensures elements == old(elements)       // Pós-condição: O array de elementos permanece o mesmo após a execução (exceto pelo elemento removido)
    ensures value == old(elements[tail])    // Pós-condição: value é igual ao elemento que estava na cauda do deque antes da execução
    ensures tail == (old(tail) - 1 + capacity) % capacity  // Pós-condição: fórmula exata da nova cauda (o corpo sempre a atualiza assim, mesmo quando o deque esvazia)
    ensures forall i {:trigger elements[i]} ::
      0 <= i < capacity && i != tail ==>
      elements[i] == old(elements[i])       // Pós-condição: Todos os elementos do deque, exceto o novo elemento na cauda, permanecem inalterados
    ensures old(size) == 1 ==> head == 0    // Pós-condição: Se o deque tinha apenas um elemento, head é resetado para 0 (indicando que o deque está vazio)
  {
    value := elements[tail];
    var oldTail := tail;
    tail := (tail - 1 + capacity) % capacity;
    if size == 1 {
      head := 0; // deque ficará vazio: head deve ser resetado para 0
    } else {
      // Mesmo truque do PushHead/PushTail: separa o caso de wrap-around
      // explicitamente em vez de deixar uma identidade não-linear para o Z3.
      if oldTail > 0 {
        assert tail == oldTail - 1;
      } else {
        assert oldTail == 0;
        assert tail == capacity - 1;
      }
    }
    size := size - 1;
  }

  method SetCapacity(newCapacity: int)
    modifies this, this.elements
    requires Valid()                     // Pré-condição: O deque deve ser válido
    requires newCapacity > 0             // Pré-condição: A nova capacidade deve ser um inteiro positivo
    requires newCapacity >= size         // Pré-condição: A nova capacidade deve ser maior ou igual ao tamanho atual do deque
    ensures Valid()                      // Pós-condição: O deque continua válido após a execução
    ensures capacity == newCapacity      // Pós-condição: A capacidade atual do deque é igual à nova capacidade
    ensures size == old(size)            // Pós-condição: O tamanho atual do deque permanece o mesmo após a execução
    ensures fresh(elements)              // Pós-condição: O array de elementos é alocado dinamicamente (fresh) e tem o tamanho igual à nova capacidade
 {
    var newElements := new int[newCapacity];

    for i := 0 to size
      invariant Valid()                   // Garante que o deque continua válido durante a cópia dos elementos
      invariant size == old(size)         // Garante que o tamanho do deque não mudou durante a cópia dos elementos
      invariant capacity == old(capacity) // Garante que a capacidade do deque não mudou durante a cópia dos elementos
      invariant head == old(head)         // Garante que o índice da cabeça do deque não mudou durante a cópia dos elementos
      invariant tail == old(tail)         // Garante que o índice da cauda do deque não mudou durante a cópia dos elementos
      invariant elements == old(elements) // Garante que o array original de elementos não mudou durante a cópia dos elementos
      invariant 0 <= i <= size            // Garante que o índice 'i' está sempre dentro dos limites do tamanho atual do deque
      invariant forall j {:trigger newElements[j]} ::
      0 <= j < i ==> 
      newElements[j] == elements[(head + j) % capacity] // Garante que os elementos copiados para o novo array são iguais aos elementos originais do deque
    {
      newElements[i] := elements[(head + i) % capacity];
    }

    elements := newElements;
    capacity := newCapacity;
    head := 0;
    tail := size - 1;
  }
}