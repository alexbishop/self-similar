#pragma once
#ifndef HEADER_GUARD_gupta_sidki
#define HEADER_GUARD_gupta_sidki

#include <string>
#include <vector>

class gupta_sidki {
private:
  std::vector<char> m_data;

  struct nonce {};
  gupta_sidki(nonce, char l);

protected:
  static bool multiply_portraits(
                  std::vector<char>& output,
                  const std::vector<char>& lhs,
                  const std::vector<char>& rhs);
  static bool inverse_portrait(
                  std::vector<char>& output, 
                  const std::vector<char>& in);

public:
  gupta_sidki();
  gupta_sidki(std::string word);

  static const gupta_sidki a, a_inverse, b, b_inverse;

  const std::vector<char>& portrait() const;

  gupta_sidki inverse() const;
  gupta_sidki& operator*=(const gupta_sidki&);
  gupta_sidki operator*( const gupta_sidki&) const;

  auto operator<=>(const gupta_sidki&) const = default;
};

#endif
