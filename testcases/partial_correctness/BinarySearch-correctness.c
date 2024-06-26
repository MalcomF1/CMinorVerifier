/*@
  predicate sorted(integer arr[], integer low, integer high) =
  	\forall integer sorted_a,sorted_b;
		((low <= sorted_a && sorted_a <= sorted_b && sorted_b <= high) ==> arr[sorted_a]<=arr[sorted_b]);
 */

/*@
  requires \valid(a+(0..n-1));
  requires 0 <= l && u < n && sorted(a, 0, n - 1);
  ensures \result == 1 <==> \exists integer ix; (l <= ix && ix <= u && a[ix] == e);
 */
int BinarySearch(int a[], int n, int l, int u, int e) {
	if (l > u)
		return 0;
	else {
		int m = (l + u) / 2;
		if (a[m] == e)
			return 1;
		else if (a[m] < e)
			return BinarySearch(a, n, m + 1, u, e);
		else
			return BinarySearch(a, n, l, m - 1, e);
	}
}
