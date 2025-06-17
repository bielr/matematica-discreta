import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.BooleanSupplier;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.IntStream;

/*
 * Aquesta entrega consisteix en implementar tots els mètodes anomenats "exerciciX". Ara mateix la
 * seva implementació consisteix en llançar `UnsupportedOperationException`, ho heu de canviar així
 * com els aneu fent.
 *
 * Criteris d'avaluació:
 *
 * - Si el codi no compila tendreu un 0.
 *
 * - Les úniques modificacions que podeu fer al codi són:
 *    + Afegir un mètode (dins el tema que el necessiteu)
 *    + Afegir proves a un mètode "tests()"
 *    + Òbviament, implementar els mètodes que heu d'implementar ("exerciciX")
 *   Si feu una modificació que no sigui d'aquesta llista, tendreu un 0.
 *
 * - Principalment, la nota dependrà del correcte funcionament dels mètodes implementats (provant
 *   amb diferents entrades).
 *
 * - Tendrem en compte la neteja i organització del codi. Un estandard que podeu seguir és la guia
 *   d'estil de Google per Java: https://google.github.io/styleguide/javaguide.html . Per exemple:
 *    + IMPORTANT: Aquesta entrega està codificada amb UTF-8 i finals de línia LF.
 *    + Indentació i espaiat consistent
 *    + Bona nomenclatura de variables
 *    + Declarar les variables el més aprop possible al primer ús (és a dir, evitau blocs de
 *      declaracions).
 *    + Convé utilitzar el for-each (for (int x : ...)) enlloc del clàssic (for (int i = 0; ...))
 *      sempre que no necessiteu l'índex del recorregut. Igualment per while si no és necessari.
 *
 * Per com està plantejada aquesta entrega, no necessitau (ni podeu) utilitzar cap `import`
 * addicional, ni qualificar classes que no estiguin ja importades. El que sí podeu fer és definir
 * tots els mètodes addicionals que volgueu (de manera ordenada i dins el tema que pertoqui).
 *
 * Podeu fer aquesta entrega en grups de com a màxim 3 persones, i necessitareu com a minim Java 10.
 * Per entregar, posau els noms i cognoms de tots els membres del grup a l'array `Entrega.NOMS` que
 * està definit a la línia 53.
 *
 * L'entrega es farà a través d'una tasca a l'Aula Digital que obrirem abans de la data que se us
 * hagui comunicat. Si no podeu visualitzar bé algun enunciat, assegurau-vos de que el vostre editor
 * de texte estigui configurat amb codificació UTF-8.
 */
class Entrega {
  static final String[] NOMS = {};

  /*
   * Aquí teniu els exercicis del Tema 1 (Lògica).
   */
  static class Tema1 {
    /*
     * Determinau si l'expressió és una tautologia o no:
     *
     * (((vars[0] ops[0] vars[1]) ops[1] vars[2]) ops[2] vars[3]) ...
     *
     * Aquí, vars.length == ops.length+1, i cap dels dos arrays és buid. Podeu suposar que els
     * identificadors de les variables van de 0 a N-1, i tenim N variables diferents (mai més de 20
     * variables).
     *
     * Cada ops[i] pot ser: CONJ, DISJ, IMPL, NAND.
     *
     * Retornau:
     *   1 si és una tautologia
     *   0 si és una contradicció
     *   -1 en qualsevol altre cas.
     *
     * Vegeu els tests per exemples.
     */
    static final char CONJ = '∧';
    static final char DISJ = '∨';
    static final char IMPL = '→';
    static final char NAND = '.';
    //Aplicamos una operacion logica binaria entre a y b
    static boolean aplica(char op, boolean a, boolean b) {
      switch (op) {
       //∧
        case CONJ: return a && b;
       //∨
        case DISJ: return a || b;
       //→
        case IMPL: return !a || b;
      //.
        case NAND: return !(a && b);
        default: throw new IllegalArgumentException("Operador desconegut: " + op);
      }
    }

    static int exercici1(char[] ops, int[] vars) {
      // Nombre de variables (máximo índice de 'vars' + 1)
      int n = Arrays.stream(vars).max().orElse(0) + 1;
  // Total de combinaciones de verdad posibles: 2^n
      int total = 1 << n;

  // Marcas para saber si siempre es cierto o siempre es falso
      boolean siempreCierto = true;
      boolean siempreFalso = true;

 // Iteramos por cada combinación de valores de verdad (truth table)
      for (int mask = 0; mask < total; mask++) {
        boolean[] val = new boolean[n];
        for (int i = 0; i < n; i++) {
      // Genera la máscara booleana para cada variable
          val[i] = (mask & (1 << i)) != 0;
        }

// Evaluamos la expresión lógica de izquierda a derecha
        boolean res = val[vars[0]];
        for (int i = 0; i < ops.length; i++) {
          res = aplica(ops[i], res, val[vars[i + 1]]);
        }
    // Verificamos si el resultado cambia según la asignación de valores
        //No es contradiccion
        if (res) {
          siempreFalso = false;
       //No es tautologia
        } else {
          siempreCierto = false;
        }
      }
      //Es una tautologia
      if (siempreCierto) return 1;
      //Es una contradiccion
      if (siempreFalso) return 0;
      return -1;
    }

    /*
     * Aquest mètode té de paràmetre l'univers (representat com un array) i els predicats
     * adients `p` i `q`. Per avaluar aquest predicat, si `x` és un element de l'univers, podeu
     * fer-ho com `p.test(x)`, que té com resultat un booleà (true si `P(x)` és cert).
     *
     * Amb l'univers i els predicats `p` i `q` donats, returnau true si la següent proposició és
     * certa.
     *
     * (∀x : P(x)) <-> (∃!x : Q(x))
     */
    static boolean exercici2(int[] universe, Predicate<Integer> p, Predicate<Integer> q) {
    // Banderas para los dos lados de la implicación, suposamos que todos cumplen P al    
    // principio
      boolean totsCompleixenP = true;
    // Contador para verificar cuántos elementos cumplen Q(x)
      int compteQ = 0;

      for (int x : universe) {
        // Si encontramos uno que NO cumple P(x), el ∀x P(x) es falso
        if (!p.test(x)) totsCompleixenP = false;
        // Si Q(x) se cumple, aumentamos el contador
        if (q.test(x)) compteQ++;
      }

    // Comprobamos unicidad: exactamente un compleix Q(x)
      return (totsCompleixenP && compteQ == 1) || (!totsCompleixenP && compteQ != 1);

    }

    static void tests() {
      // Exercici 1
      // Taules de veritat

      // Tautologia: ((p0 → p2) ∨ p1) ∨ p0
      test(1, 1, 1, () -> exercici1(new char[] { IMPL, DISJ, DISJ }, new int[] { 0, 2, 1, 0 }) == 1);
      // Contradicció: (p0 . p0) ∧ p0
      test(1, 1, 2, () -> exercici1(new char[] { NAND, CONJ }, new int[] { 0, 0, 0 }) == 0);
      // Test 2: (p0 . p0) ∧ p0 és una contradicción → esperamos 0
      test(1, 1, 2, () -> exercici1(new char[] { NAND, CONJ }, new int[] { 0, 0, 0 }) == 0);
      // Test 3: (p0 ∧ p1) → p0 no es ni tautología ni contradicción → esperamos -1 (Error)
      test(1, 1, 3, () -> exercici1(new char[] { CONJ, IMPL }, new int[] { 0, 1, 0 }) == -1);      

      // Exercici 2
      // Equivalència
      // Test 1: P(x) ≡ x == 0, Q(x) ≡ x == 0 sobre {1,2,3}
      // ∀x P(x) es falso (ningun x vale 0) y ∃!x Q(x) tambien es falso (ningun x Q)
      // false <-> false = true → esperamos true
      test(1, 2, 1, () -> {
        return exercici2(new int[] { 1, 2, 3 }, (x) -> x == 0, (x) -> x == 0);
      });
      
      // Test 2: P(x) ≡ x >= 1 (todos cumplen P); Q(x) ≡ x % 2 == 0 (hay 1 y 2, dos elementos)
      // ∀x P(x) = true, ∃!x Q(x) = false (tenemos +1 de Q) → true <-> false = false →    
      // esperamos false

      test(1, 2, 2, () -> {
        return exercici2(new int[] { 1, 2, 3 }, (x) -> x >= 1, (x) -> x % 2 == 0);
      });
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 2 (Conjunts).
   *
   * Per senzillesa tractarem els conjunts com arrays (sense elements repetits). Per tant, un
   * conjunt de conjunts d'enters tendrà tipus int[][]. Podeu donar per suposat que tots els
   * arrays que representin conjunts i us venguin per paràmetre estan ordenats de menor a major.
   *
   * Les relacions també les representarem com arrays de dues dimensions, on la segona dimensió
   * només té dos elements. L'array estarà ordenat lexicogràficament. Per exemple
   *   int[][] rel = {{0,0}, {0,1}, {1,1}, {2,2}};
   * i també donarem el conjunt on està definida, per exemple
   *   int[] a = {0,1,2};
   * Als tests utilitzarem extensivament la funció generateRel definida al final (també la podeu
   * utilitzar si la necessitau).
   *
   * Les funcions f : A -> B (on A i B son subconjunts dels enters) les representam o bé amb el seu
   * graf o bé amb un objecte de tipus Function<Integer, Integer>. Sempre donarem el domini int[] a
   * i el codomini int[] b. En el cas de tenir un objecte de tipus Function<Integer, Integer>, per
   * aplicar f a x, és a dir, "f(x)" on x és d'A i el resultat f.apply(x) és de B, s'escriu
   * f.apply(x).
   */
  static class Tema2 {
    /*
     * Trobau el nombre de particions diferents del conjunt `a`, que podeu suposar que no és buid.
     *
     * Pista: Cercau informació sobre els nombres de Stirling.
     */
    static int exercici1(int[] a) {
    int n= a.length;
    // Creamos una tabla de números de Bell hasta n (suma de Stirling 2a especie)
    int[] bell = new int[n + 1];
    bell[0] = 1;

    for (int i = 1; i <= n; i++) {
      int[] next = new int[n + 1];
      for (int j = 0; j < i; j++) {
        next[j + 1] += bell[j];
        next[j] += j * bell[j];
      }
      bell = next;
    }
      
    return bell[n];
    }

    /*
     * Trobau el cardinal de la relació d'ordre parcial sobre `a` més petita que conté `rel` (si
     * existeix). En altres paraules, el cardinal de la seva clausura reflexiva, transitiva i
     * antisimètrica.
     *
     * Si no existeix, retornau -1.
     */
    static int exercici2(int[] a, int[][] rel) {
    int n = a.length;
    boolean[][] mat = new boolean[n][n];

    // Copiamos la relación inicial
    for (int[] pair : rel) {
      mat[pair[0]][pair[1]] = true;
    }

    // Clausura reflexiva
    for (int i = 0; i < n; i++) mat[i][i] = true;

    // Clausura transitiva (algoritmo de Floyd-Warshall)
    for (int k = 0; k < n; k++)
      for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
          if (mat[i][k] && mat[k][j]) mat[i][j] = true;

    // Verificamos antisimetría: si aRy y yRa entonces a == y
    for (int i = 0; i < n; i++)
      for (int j = 0; j < n; j++)
        if (i != j && mat[i][j] && mat[j][i])
          return -1;

    // Contamos el número de pares verdaderos
    int count = 0;
    for (int i = 0; i < n; i++)
      for (int j = 0; j < n; j++)
        if (mat[i][j]) count++;

    return count;

    }

    /*
     * Donada una relació d'ordre parcial `rel` definida sobre `a` i un subconjunt `x` de `a`,
     * retornau:
     * - L'ínfim de `x` si existeix i `op` és false
     * - El suprem de `x` si existeix i `op` és true
     * - null en qualsevol altre cas
     */
    static Integer exercici3(int[] a, int[][] rel, int[] x, boolean op) {
    Set<Integer> relSet = new HashSet<>();
    Map<Integer, Set<Integer>> dominates = new HashMap<>();

    for (int i = 0; i < a.length; i++) {
    dominates.put(a[i], new HashSet<>());
    }

    for (int i = 0; i < rel.length; i++) {
    int from = rel[i][0];
    int to = rel[i][1];
    dominates.get(from).add(to);
    }

    List<Integer> candidates = new ArrayList<>();

    for (int i = 0; i < a.length; i++) {
    int m = a[i];
    boolean ok = true;

    for (int j = 0; j < x.length; j++) {
        int xi = x[j];
      
        //Supremo: xi ≤ m
        if (op) {
            if (!dominates.get(xi).contains(m) && xi != m) {
                ok = false;
                break;
            }
          //Infimo: m ≤ xi
        } else {
            if (!dominates.get(m).contains(xi) && m != xi) {
                ok = false;
                break;
            }
        }
    }

    if (ok) {
        candidates.add(m);
    }
}

    if (candidates.isEmpty()) return null;
    return op ? Collections.min(candidates) : Collections.max(candidates);
    // La línea de arriba lo que hace es que si op es true, devolvemos el mínimo de los candidatos (supremo)
    // Y en el caso de que si op es false, devolvemos el máximo de los candidatos (ínfimo)
}

    /*
     * Donada una funció `f` de `a` a `b`, retornau:
     *  - El graf de la seva inversa (si existeix)
     *  - Sinó, el graf d'una inversa seva per l'esquerra (si existeix)
     *  - Sinó, el graf d'una inversa seva per la dreta (si existeix)
     *  - Sinó, null.
     */
    static int[][] exercici4(int[] a, int[] b, Function<Integer, Integer> f) {
    var graf = new ArrayList<int[]>();
    var fwd = new HashMap<Integer, Integer>();
    var rev = new HashMap<Integer, Integer>();

    for (int x : a) {
      int y = f.apply(x);
      fwd.put(x, y);
      if (rev.containsKey(y)) {
        //Marca conflicto
        rev.put(y, -1);
      } else {
        rev.put(y, x);
      }
    }

    boolean isInjective = true;
    for (var e : rev.entrySet()) {
      if (e.getValue() == -1) {
        isInjective = false;
        break;
      }
    }

    boolean isSurjective = true;
    for (int y : b) {
      if (!rev.containsKey(y)) {
        isSurjective = false;
        break;
      }
    }

    if (isInjective && isSurjective) {
      for (int y : b) {
        graf.add(new int[] { y, rev.get(y) });
      }
    } else if (isInjective) { // inversa per l'esquerra
      for (var e : rev.entrySet()) {
        if (e.getValue() != -1) {
          graf.add(new int[] { e.getKey(), e.getValue() });
        }
      }
    } else if (isSurjective) { // inversa per la dreta
      for (int x : a) {
        graf.add(new int[] { f.apply(x), x });
      }
    } else {
      return null;
    }

    // Ordenamos lexicográficamente
    return lexSorted(graf.toArray(new int[0][]));
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // Nombre de particions
      test(2, 1, 1, () -> exercici1(new int[] { }) ==1);
      test(2, 1, 1, () -> exercici1(new int[] { 1 }) == 1);
      test(2, 1, 3, () -> exercici1(new int[] { 1, 2}) == 2);
      test(2, 1, 2, () -> exercici1(new int[] { 1, 2, 3 }) == 5);

      // Exercici 2
      // Clausura d'ordre parcial

      final int[] INT02 = { 0, 1, 2 };

      test(2, 2, 1, () -> exercici2(INT02, new int[][] { {0, 1}, {1, 2} }) == 6);
      test(2, 2, 2, () -> exercici2(INT02, new int[][] { {0, 1}, {1, 0}, {1, 2} }) == -1);

      // Exercici 3
      // Ínfims i suprems

      final int[] INT15 = { 1, 2, 3, 4, 5 };
      final int[][] DIV15 = generateRel(INT15, (n, m) -> m % n == 0);
      final Integer ONE = 1;

      test(2, 3, 1, () -> ONE.equals(exercici3(INT15, DIV15, new int[] { 2, 3 }, false)));
      test(2, 3, 2, () -> exercici3(INT15, DIV15, new int[] { 2, 3 }, true) == null);

      // Exercici 4
      // Inverses

      final int[] INT05 = { 0, 1, 2, 3, 4, 5 };

      test(2, 4, 1, () -> {
        var inv = exercici4(INT05, INT02, (x) -> x/2);

        if (inv == null)
          return false;

        inv = lexSorted(inv);

        if (inv.length != INT02.length)
          return false;

        for (int i = 0; i < INT02.length; i++) {
          if (inv[i][0] != i || inv[i][1]/2 != i)
            return false;
        }

        return true;
      });

      test(2, 4, 2, () -> {
        var inv = exercici4(INT02, INT05, (x) -> x);

        if (inv == null)
          return false;

        inv = lexSorted(inv);

        if (inv.length != INT05.length)
          return false;

        for (int i = 0; i < INT02.length; i++) {
          if (inv[i][0] != i || inv[i][1] != i)
            return false;
        }

        return true;
      });
    }

    /*
     * Ordena lexicogràficament un array de 2 dimensions
     * Per exemple:
     *  arr = {{1,0}, {2,2}, {0,1}}
     *  resultat = {{0,1}, {1,0}, {2,2}}
     */
    static int[][] lexSorted(int[][] arr) {
      if (arr == null)
        return null;

      var arr2 = Arrays.copyOf(arr, arr.length);
      Arrays.sort(arr2, Arrays::compare);
      return arr2;
    }

    /*
     * Genera un array int[][] amb els elements {a, b} (a de as, b de bs) que satisfàn pred.test(a, b)
     * Per exemple:
     *   as = {0, 1}
     *   bs = {0, 1, 2}
     *   pred = (a, b) -> a == b
     *   resultat = {{0,0}, {1,1}}
     */
    static int[][] generateRel(int[] as, int[] bs, BiPredicate<Integer, Integer> pred) {
      var rel = new ArrayList<int[]>();

      for (int a : as) {
        for (int b : bs) {
          if (pred.test(a, b)) {
            rel.add(new int[] { a, b });
          }
        }
      }

      return rel.toArray(new int[][] {});
    }

    // Especialització de generateRel per as = bs
    static int[][] generateRel(int[] as, BiPredicate<Integer, Integer> pred) {
      return generateRel(as, as, pred);
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 3 (Grafs).
   *
   * Els (di)grafs vendran donats com llistes d'adjacència (és a dir, tractau-los com diccionaris
   * d'adjacència on l'índex és la clau i els vèrtexos estan numerats de 0 a n-1). Per exemple,
   * podem donar el graf cicle no dirigit d'ordre 3 com:
   *
   * int[][] c3dict = {
   *   {1, 2}, // veïns de 0
   *   {0, 2}, // veïns de 1
   *   {0, 1}  // veïns de 2
   * };
   */
  static class Tema3 {
    /*
     * Determinau si el graf `g` (no dirigit) té cicles.
     */
    static boolean exercici1(int[][] g) {
      int n = g.length;
            boolean[] visitat = new boolean[n];

            for (int v = 0; v < n; v++) {
                if (!visitat[v]) {
                    if (dfsCicle(g, v, visitat, -1)) {
                        return true;
                    }
                }
            }
            return false;
        }

        static boolean dfsCicle(int[][] g, int actual, boolean[] visitat, int pare) {
            visitat[actual] = true;

            for (int veí : g[actual]) {
                if (!visitat[veí]) {
                    if (dfsCicle(g, veí, visitat, actual)) {
                        return true;
                    }
                } else if (veí != pare) {
                    //Ciclo detectado
                    return true;
                }
            }
            return false;
    }

    /*
     * Determinau si els dos grafs són isomorfs. Podeu suposar que cap dels dos té ordre major que
     * 10.
     */
    static boolean exercici2(int[][] g1, int[][] g2) {
        int n = g1.length;
            if (g2.length != n) {
                return false;
            }

            int[] perm = new int[n];
            for (int i = 0; i < n; i++) {
                perm[i] = i;
            }

            while (nextPerm(perm)){
                if (sónIsomorfs(g1, g2, perm)) {
                    return true;
                }
            } 

            return false;
        }

        static boolean sónIsomorfs(int[][] g1, int[][] g2, int[] perm) {
            int n = g1.length;
            for (int i = 0; i < n; i++) {
                java.util.Set<Integer> veïns1 = new java.util.HashSet<>();
                for (int v : g1[i]) {
                    veïns1.add(perm[v]);
                }

                java.util.Set<Integer> veïns2 = new java.util.HashSet<>();
                for (int v : g2[perm[i]]) {
                    veïns2.add(v);
                }

                if (!veïns1.equals(veïns2)) {
                    return false;
                }
            }
            return true;
        }

        // Genera la siguiente permutacion en orden lexicografico 
        static boolean nextPerm(int[] a) {
            int i = a.length - 2;
            while (i >= 0 && a[i] >= a[i + 1]) {
                i--;
            }
            if (i < 0) {
                return false;
            }
            int j = a.length - 1;
            while (a[j] <= a[i]) {
                j--;
            }
            int tmp = a[i];
            a[i] = a[j];
            a[j] = tmp;
            for (int l = i + 1, r = a.length - 1; l < r; l++, r--) {
                tmp = a[l];
                a[l] = a[r];
                a[r] = tmp;
            }
            return true;
    }


    /*
     * Determinau si el graf `g` (no dirigit) és un arbre. Si ho és, retornau el seu recorregut en
     * postordre desde el vèrtex `r`. Sinó, retornau null;
     *
     * En cas de ser un arbre, assumiu que l'ordre dels fills vé donat per l'array de veïns de cada
     * vèrtex.
     */
    static int[] exercici3(int[][] g, int r) {
      int n = g.length;
      boolean[] visitat = new boolean[n];
      java.util.List<Integer> postordre = new java.util.ArrayList<>();

        if (!dfs(g, r, -1, visitat, postordre)) {
             return null;
         }
         for (boolean v : visitat) {
            if (!v) {
                return null;
               }
         }

        int[] resultat = new int[n];
        for (int i = 0; i < n; i++) {
             resultat[i] = postordre.get(i);
           }
          return resultat;
        }

       static boolean dfs(int[][] g, int u, int pare, boolean[] visitat, java.util.List<Integer> post) {
           if (visitat[u]) {
              return false;
           }
           visitat[u] = true;
           for (int v : g[u]) {
                if (v != pare) {
                    if (!dfs(g, v, u, visitat, post)) {
                        return false;
                    }
                }
            }
        //postorden
        post.add(u);
        return true;
    }

    /*
     * Suposau que l'entrada és un mapa com el següent, donat com String per files (vegeu els tests)
     *
     *   _____________________________________
     *  |          #       #########      ####|
     *  |       O  # ###   #########  ##  ####|
     *  |    ####### ###   #########  ##      |
     *  |    ####  # ###   #########  ######  |
     *  |    ####    ###              ######  |
     *  |    ######################## ##      |
     *  |    ####                     ## D    |
     *  |_____________________________##______|
     *
     * Els límits del mapa els podeu considerar com els límits de l'array/String, no fa falta que
     * cerqueu els caràcters "_" i "|", i a més podeu suposar que el mapa és rectangular.
     *
     * Donau el nombre mínim de caselles que s'han de recorrer per anar de l'origen "O" fins al
     * destí "D" amb les següents regles:
     *  - No es pot sortir dels límits del mapa
     *  - No es pot passar per caselles "#"
     *  - No es pot anar en diagonal
     *
     * Si és impossible, retornau -1.
     */
    static int exercici4(char[][] mapa) {
      int rows = mapa.length, cols = mapa[0].length;
      int[][] dirs = {{0, 1}, {1, 0}, {0, -1}, {-1, 0}};
      java.util.Queue<int[]> q = new java.util.LinkedList<>();
      boolean[][] vist = new boolean[rows][cols];
     // Encontrar el origen
        outer:
        for (int i = 0; i < rows; i++) {
            for (int j = 0; j < cols; j++) {
                 if (mapa[i][j] == 'O') {
                     q.add(new int[]{i, j, 0});
                     vist[i][j] = true;
                     break outer;
                 }
            }
        }

       while (!q.isEmpty()) {
           int[] node = q.poll();
           int x = node[0], y = node[1], d = node[2];

            if (mapa[x][y] == 'D') {
                return d;
             }

             for (int[] dir : dirs) {
                int nx = x + dir[0], ny = y + dir[1];
                 if (nx >= 0 && nx < rows && ny >= 0 && ny < cols
                      && !vist[nx][ny] && mapa[nx][ny] != '#') {
                        vist[nx][ny] = true;
                        q.add(new int[]{nx, ny, d + 1});
                }
            }
        }
      //destino no accessible
      return -1; 

    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {

      final int[][] D2 = { {}, {} };
      final int[][] C3 = { {1, 2}, {0, 2}, {0, 1} };

      final int[][] T1 = { {1, 2}, {0}, {0} };
      final int[][] T2 = { {1}, {0, 2}, {1} };

      // Exercici 1
      // G té cicles?

      test(3, 1, 1, () -> !exercici1(D2));
      test(3, 1, 2, () -> exercici1(C3));

      // Exercici 2
      // Isomorfisme de grafs

      test(3, 2, 1, () -> exercici2(T1, T2));
      test(3, 2, 2, () -> !exercici2(T1, C3));

      // Exercici 3
      // Postordre

      test(3, 3, 1, () -> exercici3(C3, 1) == null);
      test(3, 3, 2, () -> Arrays.equals(exercici3(T1, 0), new int[] { 1, 2, 0 }));

      // Exercici 4
      // Laberint

      test(3, 4, 1, () -> {
        return -1 == exercici4(new char[][] {
            " #O".toCharArray(),
            "D# ".toCharArray(),
            " # ".toCharArray(),
        });
      });

      test(3, 4, 2, () -> {
        return 8 == exercici4(new char[][] {
            "###D".toCharArray(),
            "O # ".toCharArray(),
            " ## ".toCharArray(),
            "    ".toCharArray(),
        });
      });
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 4 (Aritmètica).
   *
   * En aquest tema no podeu:
   *  - Utilitzar la força bruta per resoldre equacions: és a dir, provar tots els nombres de 0 a n
   *    fins trobar el que funcioni.
   *  - Utilitzar long, float ni double.
   *
   * Si implementau algun dels exercicis així, tendreu un 0 d'aquell exercici.
   */
  static class Tema4 {
    /*
     * Primer, codificau el missatge en blocs de longitud 2 amb codificació ASCII. Després encriptau
     * el missatge utilitzant xifrat RSA amb la clau pública donada.
     *
     * Per obtenir els codis ASCII del String podeu utilitzar `msg.getBytes()`.
     *
     * Podeu suposar que:
     * - La longitud de `msg` és múltiple de 2
     * - El valor de tots els caràcters de `msg` està entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
     *
     * Pista: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
     */
    static int[] exercici1(String msg, int n, int e) {
          //Transforma el string msg en un array con cada letra en ASCII
          byte[] bytes = msg.getBytes(); 
          //Declaramos el array que contendra las letras encriptadas      
          int[] encr = new int[bytes.length / 2]; 

          for (int i = 0; i < encr.length; i++) {

              int letra1 = bytes[i * 2];
              int letra2 = bytes[i * 2 + 1];
              int base = letra1 * 128 + letra2;
              int result = expSquar(base, e, n);
              encr[i] = result;
          }
          return encr;

      }

      public static int expSquar(int base, int exp, int mod) {
          //Todo el codigo esta basado en el Exponentiation by squaring
          int result = 1;
          //Comprobamos que la base esté bien 
          base = base % mod; 

          while (exp > 0) {

              if ((exp & 1) == 1) { 
                  // Si el exp es impar, multiplicamos result por base
                  result = (result * base) % mod;
              }
              // Elevamos base al cuadrado
              base = (base * base) % mod; 
              // Dividimos el exp por 2
              exp = exp / 2;
          }

          return result;
    }

}

    /*
     * Primer, desencriptau el missatge utilitzant xifrat RSA amb la clau pública donada. Després
     * descodificau el missatge en blocs de longitud 2 amb codificació ASCII (igual que l'exercici
     * anterior, però al revés).
     *
     * Per construir un String a partir d'un array de bytes podeu fer servir el constructor
     * `new String(byte[])`. Si heu de factoritzar algun nombre, ho podeu fer per força bruta.
     *
     * També podeu suposar que:
     * - La longitud del missatge original és múltiple de 2
     * - El valor de tots els caràcters originals estava entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
     */
    static String exercici2(int[] m, int n, int e) {
       //Factorizar n (fuerza bruta)
        boolean encontrado = false;
        int p=0,q=0;
      
        for (int i = 2; i <= (int)Math.sqrt(n) && !encontrado; i++) {
            if (n % i == 0) {
                p = i;
                q = n/i;
                encontrado = true;
            }     
        }     
        int phi = (p - 1) * (q - 1); //phi es φ(n)
        int d = Inverso(e, phi);
        // Desencriptar
        //Creamos el array que tendrá las letras desmiptadas
        byte[] decr = new byte[m.length * 2];
      
    for (int i = 0; i < m.length; i++) {
        int decrypted = expSquar(m[i], d, n);
        byte char1 = (byte) (decrypted / 128);
        byte char2 = (byte) (decrypted % 128);
        decr[i * 2] = char1;
        decr[i * 2 + 1] = char2;
    }
    //Transforma el array desencriptado en un string como en el ejercico 1 pero al reves
    return new String(decr);
    }
    public static int[] mcdExtendido(int a, int b) {
        if (b == 0) {//Cuando la división no tiene resto (a%b=0)
            return new int[]{a, 1, 0};
        }
        int[] vals = mcdExtendido(b, a % b);
        int mcd = vals[0];
        int x = vals[2];
        int y = vals[1] - (a / b) * vals[2];
        return new int[]{mcd, x, y};
    }

    
    public static int Inverso(int e, int phi) {
        int[] result = mcdExtendido(e, phi);//Calculamos el mcd y los coeficientes de x y
        int mcd = result[0];
        int x = result[1];
        if (mcd != 1) { //En el caso de que no se pueda invertir
            throw new ArithmeticException("No existe inversa modular: e y φ(n) no son coprimos");
        }
        return (x % phi + phi) % phi; //Esto sirve para que el inverso sea positivo

    }

    static void tests() {
      // Exercici 1
      // Codificar i encriptar
      test(4, 1, 1, () -> {
        var n = 2*8209;
        var e = 5;

        var encr = exercici1("Patata", n, e);
        return Arrays.equals(encr, new int[] { 4907, 4785, 4785 });
      });

      // Exercici 2
      // Desencriptar i decodificar
      test(4, 2, 1, () -> {
        var n = 2*8209;
        var e = 5;

        var encr = new int[] { 4907, 4785, 4785 };
        var decr = exercici2(encr, n, e);
        return "Patata".equals(decr);
      });
    }
  }

  /*
   * Aquest mètode `main` conté alguns exemples de paràmetres i dels resultats que haurien de donar
   * els exercicis. Podeu utilitzar-los de guia i també en podeu afegir d'altres (no els tendrem en
   * compte, però és molt recomanable).
   *
   * Podeu aprofitar el mètode `test` per comprovar fàcilment que un valor sigui `true`.
   */
  public static void main(String[] args) {
    System.out.println("---- Tema 1 ----");
    Tema1.tests();
    System.out.println("---- Tema 2 ----");
    Tema2.tests();
    System.out.println("---- Tema 3 ----");
    Tema3.tests();
    System.out.println("---- Tema 4 ----");
    Tema4.tests();
  }

  // Informa sobre el resultat de p, juntament amb quin tema, exercici i test es correspon.
  static void test(int tema, int exercici, int test, BooleanSupplier p) {
    try {
      if (p.getAsBoolean())
        System.out.printf("Tema %d, exercici %d, test %d: OK\n", tema, exercici, test);
      else
        System.out.printf("Tema %d, exercici %d, test %d: Error\n", tema, exercici, test);
    } catch (Exception e) {
      if (e instanceof UnsupportedOperationException && "pendent".equals(e.getMessage())) {
        System.out.printf("Tema %d, exercici %d, test %d: Pendent\n", tema, exercici, test);
      } else {
        System.out.printf("Tema %d, exercici %d, test %d: Excepció\n", tema, exercici, test);
        e.printStackTrace();
      }
    }
  }
}

// vim: set textwidth=100 shiftwidth=2 expandtab :
