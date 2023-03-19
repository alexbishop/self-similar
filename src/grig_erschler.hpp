#pragma once
#ifndef HEADER_GUARD_grig_erschler
#define HEADER_GUARD_grig_erschler

#include <string>
#include <vector>

class grig01 {
private:
  std::vector<char> m_data;

  struct nonce {};
  grig01(nonce, char l);

protected:
  static bool multiply_portraits(
                  std::vector<char>& output,
                  const std::vector<char>& lhs,
                  const std::vector<char>& rhs);
  static bool inverse_portrait(
                  std::vector<char>& output, 
                  const std::vector<char>& in);

public:
  grig01();
  grig01(std::string word);

  static const grig01 a, b, c, d;

  const std::vector<char>& portrait() const;

  grig01 inverse() const;
  grig01& operator*=(const grig01&);
  grig01 operator*( const grig01&) const;

  auto operator<=>(const grig01&) const = default;
};

#endif
