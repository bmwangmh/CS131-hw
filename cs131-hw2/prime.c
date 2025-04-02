#include <stdio.h>

const int MAX=1000;

void nth_prime(int n) 
{
    int is_prime[1000];
    is_prime[0]=is_prime[1]=0;
    for (int i = 2; i <= MAX; ++i) 
        is_prime[i]=1;
    for (int i = 2; i <= MAX; ++i) 
    {
        if (is_prime[i]) 
        {
            --n;
            if(n==0)
                return i;
            prime.push_back(i);
            for (int j = i * i; j <= n; j += i)
                is_prime[j] = 1;
        }
    }
    return -1;
}

//#define FILES_IO 2
int main()
{
    int x;
    scanf("%d",&x);
    printf("%d\n",nth_prime(x));

	return 0;
}
