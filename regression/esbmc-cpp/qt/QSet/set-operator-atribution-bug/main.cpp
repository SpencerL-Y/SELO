// constructing QSets
#include <iostream>
#include <QSet>
#include <cassert>
using namespace std;

int main ()
{
    QSet<int> first;
    assert(first.size() == 0);
    QSet<int> second;
    second.insert(1);
    first = second;
    assert(first.size() == 0);
    return 0;
}
