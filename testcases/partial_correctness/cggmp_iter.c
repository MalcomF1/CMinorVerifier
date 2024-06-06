/*@
  requires i1 == 1 && j1 == 2;
*/
void foo(int i1, int j1) { // to complement the parameters

    /*@
        loop invariant i1 + 2 * j1 == 5;
    */
    while (j1 >= i1) { // to complement loop condition based on SMT translation
        i1 = i1 + 2;
        j1 = j1 - 1;
    }
    //@ assert j1 == 1; // to complement assertion to verify, deduced from fail condition
}