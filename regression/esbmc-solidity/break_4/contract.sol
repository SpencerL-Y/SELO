// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.6.0;
contract MyContract {
  uint a = 0;
  function test_break() public
  {
    for(uint i = 0; i < 10; i++)
    {
      if(i == 7)
      {
        break;
      }

      a += 1;
    }

    assert(a == 6);
  }
}