#pragma once
#ifndef HEADER_GUARD_grigorchuk
#define HEADER_GUARD_grigorchuk

#include <string>
#include <vector>

class grigorchuk {
private:
  std::vector<char> m_data;

  struct nonce {};
  grigorchuk(nonce, char l);

protected:
  static bool multiply_portraits(
                  std::vector<char>& output,
                  const std::vector<char>& lhs,
                  const std::vector<char>& rhs);
  static bool inverse_portrait(
                  std::vector<char>& output, 
                  const std::vector<char>& in);

public:
  grigorchuk();
  grigorchuk(std::string word);

  static const grigorchuk a, b, c, d;

  const std::vector<char>& portrait() const;

  grigorchuk inverse() const;
  grigorchuk& operator*=(const grigorchuk&);
  grigorchuk operator*( const grigorchuk&) const;

  auto operator<=>(const grigorchuk&) const = default;
};

#endif
