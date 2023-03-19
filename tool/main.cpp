/* clang-format off */ 
#include <iostream>
#include <vector>

#include "generate.hpp"

int main() {
  const std::vector<group_desc> groups{
    {
      .filename="fab_gup",
      .classname="fab_gup",
      .degree=3,
      .generators={
        {'a', {{'1', '1', '1'}, "(0 1 2)"}},
        {'b', {{'a', '1', 'b'}}}
      }
    },
    {
      .filename="grigorchuk",
      .classname="grigorchuk",
      .degree=2,
      .generators={
        {'a', {{'1', '1'}, "(0 1)"}},
        {'b', {{'a', 'c'}}},
        {'c', {{'a', 'd'}}},
        {'d', {{'1', 'b'}}}
      }
    },
    {
      .filename="gupta_sidki",
      .classname="gupta_sidki",
      .degree=3,
      .generators={
        {'a', {{'1', '1', '1'}, "(0 1 2)"}},
        {'b', {{'a', 'A', 'b'}}}
      }
    },
    {
      .filename="grig_erschler",
      .classname="grig01",
      .degree=2,
      .generators={
        {'a', {{'1', '1'}, "(0 1)"}},
        {'b', {{'a', 'c'}}},
        {'c', {{'1', 'b'}}},
        {'d', {{'a', 'd'}}}
      }
    }
  };

  for (const auto& desc : groups) {
    write_implementation(desc);
  }
}

