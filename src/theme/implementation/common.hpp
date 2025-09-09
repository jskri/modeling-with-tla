#ifndef COMMON_HPP
#define COMMON_HPP
#include <array>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <ostream>
#include <set>
#include <stdexcept>
#include <string>
#include <string_view>
#include <zmqpp/zmqpp.hpp>

namespace theme {
  using Id = uint32_t;
  using Context = zmqpp::context;
  using Socket = zmqpp::socket;
  using Message = zmqpp::message;
  using SocketType =  zmqpp::socket_type;
  using Endpoint = zmqpp::endpoint_t;

  // spec: Pack
  // Data is stored in a string instead of a vector<byte>, because it is more
  // convenient with respect to insertion / extraction (see below).
  struct Pack {
    Id id;
    std::string data;
    uint32_t version;
    auto operator<=>(Pack const&) const = default;
  };

  // The insertion and extraction operators are not symmetric for simplicity of
  // implementation.
  inline
  std::istream& operator>>(std::istream& i, Pack& p) {
    return i >> p.id >> p.data >> p.version;
  }

  inline
  std::ostream& operator<<(std::ostream& o, Pack const& p) {
    return o << "<<" << p.id << ",\"" << p.data << "\"," << p.version << ">>";
  }

  enum MessageType: uint8_t {
    List = 0,
    Get = 1
  };

  // The identity function.
  struct FunId {
    template<typename A>
    auto operator()(A a) const -> A {return a;}
  };

  template<typename A, std::invocable<A> F = FunId>
  auto logSet(std::set<A> const& set, std::ostream& out, F proj = {}) -> std::ostream& {
    auto first = true;
    out << "{";
    for (auto const& a: set) {
      if (!first) out << ",";
      out << proj(a);
      first = false;
    }
    out << "}";
    return out;
  }

  template<typename T>
  concept OStreamable =
    requires(std::ostream& os, T value) {
      { os << value } -> std::convertible_to<std::ostream &>;
    };

  template<OStreamable A>
  std::ostream& operator<<(std::ostream& o, std::set<A> const& set) {
    return logSet(set, o);
  }

  inline
  auto timestamp() {
    return std::chrono::steady_clock::now().time_since_epoch().count();
  }

  inline
  auto readPacks(std::string_view filepath, std::set<Pack> const& packs) -> std::set<Pack> {
    auto packFile = std::ifstream(filepath.data());
    if (packFile.fail()) {
      std::cerr << "Cannot open pack file: " << filepath << ". Skipping.\n";
      return {};
    }
    auto readPacks = std::set<Pack>{};
    auto pack = Pack{};
    while (packFile >> pack) {
      if (packs.find(pack) == packs.end()) {
        readPacks.insert(std::move(pack));
        break;
      }
    }
    return readPacks;
  }

  inline
  auto sleep_time() {
    using namespace std::chrono_literals;
    return 1s;
  }
} // namespace theme

#endif // COMMON_HPP
