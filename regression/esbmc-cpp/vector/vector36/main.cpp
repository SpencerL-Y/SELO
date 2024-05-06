// erasing from vector
#include <iostream>
#include <vector>
#include <cassert>
using namespace std;

int main ()
{
  unsigned int i;
  vector<unsigned int> myvector;

  // set some values (from 1 to 10)
  for (i=1; i<=10; i++) myvector.push_back(i);
  
  // erase the 6th element
  myvector.erase (myvector.begin()+5);
  assert(myvector[5] == 7);
  // erase the first 3 elements:
  myvector.erase (myvector.begin(),myvector.begin()+3);
  assert(myvector[2] == 7);
  cout << "myvector contains:";
  for (i=0; i<myvector.size(); i++)
    cout << " " << myvector[i];
  cout << endl;

  return 0;
}
