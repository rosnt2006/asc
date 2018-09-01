#include "calculator.hpp"

#include <cstdint>

int main()
{
  using calculator = xc::calculator<uint64_t, 4>;
  using var = calculator::var;
  calculator c;
  auto eq = [&](var x, var y) {c.forAll([&](var) {c.opBimp( [&]{c<x;}, [&]{c<y;} );} );};
  auto qe = [&](var x, var y) {c.forAll([&](var) {c.opBimp( [&]{x<c;}, [&]{y<c;} );} );};
  auto ex = [&](var x, var y) {c.opImp( [&]{eq(x, y);}, [&]{qe(x, y);} );};
  c.forAll([&](var x) {c.forAll([&](var y) {ex(x, y);} );} );
  return 0;
}
