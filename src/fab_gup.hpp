#pragma once
#ifndef HEADER_GUARD_fab_gup
#define HEADER_GUARD_fab_gup

#include <string>
#include <vector>

class fab_gup {
private:
  std::vector<char> m_data;

  struct nonce {};
  fab_gup(nonce, char l);

protected:
  static bool multiply_portraits(
                  std::vector<char>& output,
                  const std::vector<char>& lhs,
                  const std::vector<char>& rhs);
  static bool inverse_portrait(
                  std::vector<char>& output, 
                  const std::vector<char>& in);

public:
  fab_gup();
  fab_gup(std::string word);

  static const fab_gup a, a_inverse, b, b_inverse;

  const std::vector<char>& portrait() const;

  fab_gup inverse() const;
  fab_gup& operator*=(const fab_gup&);
  fab_gup operator*( const fab_gup&) const;

  auto operator<=>(const fab_gup&) const = default;
};

#endif
