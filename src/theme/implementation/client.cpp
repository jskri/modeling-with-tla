#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <optional>
#include <ostream>
#include <stdexcept>
#include <thread>
#include <zmqpp/zmqpp.hpp>
#include "common.hpp"

// This is an implementation of the internal fragment (i.e. excluding the
// environment part) of Theme3!Device2 (see `ThemeDevice2.tla`):
//
// spec: \/ Theme3!Device2!DeviceSendsListRequest
//       \/ Theme3!Device2!DeviceReceivesListReply
//       \/ Theme3!Device2!DeviceSendsGetRequest
//       \/ Theme3!Device2!DeviceReceivesGetReply

// spec: `request` and `reply` are represented in the underlying messaging
// system, and so are not explicitly present in the following code.

using namespace theme;

struct State {
  std::set<Pack> packs;
  std::set<Id> knownIds;
};

// For checking conformance of implementation to the spec.
auto logState(std::string_view event, State const& state, std::optional<Id> optId = {}) -> void {
  std::cout << timestamp()
            << ":" << event
            << ":packs=" << state.packs
            << ":knownIds=" << state.knownIds;
  if (optId.has_value())
    std::cout << ":id=" << optId.value();
  std::cout << std::endl;
}

// spec: Theme3!Device2!DeviceSendsListRequest
auto sendListRequest(Socket& socket, State const& state) -> void {
  // spec: request' = [op |-> "list"]
  auto msg = Message{};
  msg << MessageType::List;
  logState("DeviceSendsListRequest", state);
  socket.send(msg);
}

// spec: Theme3!Device2!DeviceReceivesListReply
auto receiveListReply(Socket& socket, State& state) -> void {
  // spec: reply \in [op : {"list"}, ids : SUBSET Id]
  auto msg = Message{};
  socket.receive(msg);
  auto msgType = MessageType{};
  msg >> (uint8_t&)msgType;
  if (msgType != MessageType::List) throw std::runtime_error("Unexpected message type.");

  // spec: knownIds' = knownIds \union reply.ids
  auto ids = std::vector<Id>(msg.parts() - 1, Id{});
  for (auto& id: ids) msg >> id;
  state.knownIds.insert(ids.begin(), ids.end());

  logState("DeviceReceivesListReply", state);
}

auto nextIdToGet(std::set<Id> const& knownIds, std::set<Pack> const& packs) -> std::optional<Id> {
  auto idNotGetYet = [&packs](auto id) {
    return std::ranges::none_of(packs, [id](auto const& pack) { return pack.id == id; });
  };
  if (auto it = std::ranges::find_if(knownIds, idNotGetYet); it != knownIds.end()) {
    return {*it};
  }
  return {};
}

// spec: Theme3!Device2!DeviceSendsGetRequest
// True iff a get request has been sent.
auto sendGetRequest(Socket& socket, State const& state) -> bool {
  // spec: \E id \in knownIds : PackFromId[id] \notin packs 
  if (auto optId = nextIdToGet(state.knownIds, state.packs); optId.has_value()) {
    // spec: request' = [op |-> "get", id |-> id]
    auto id = optId.value();
    auto msg = Message{};
    msg << MessageType::Get << id;
    logState("DeviceSendsGetRequest", state, id);
    socket.send(msg);
    return true;
  }
  return false;
}

// spec: Theme3!Device2!DeviceReceivesGetReply
auto receiveGetReply(Socket& socket, State& state) -> void {
  // spec: reply \in [op : {"get"}, pack : Pack]
  auto msg = Message{};
  socket.receive(msg);
  auto msgType = MessageType{};
  msg >> (uint8_t&)msgType;
  if (msgType != MessageType::Get) throw std::runtime_error("Unexpected message type.");

  // spec: packs' = packs \union {reply.pack}
  auto pack = Pack{};
  msg >> pack.id >> pack.data >> pack.version;
  state.packs.emplace(std::move(pack));

  logState("DeviceReceivesGetReply", state);
}

auto main(int argc, char* argv[]) -> int {
  if (argc != 3) {
    std::cerr << "Usage: " << argv[0] << " <initial_pack_file> <server_endpoint>\n";
    return EXIT_FAILURE;
  }
  auto initialPackFilePath = std::string_view(argv[1]);
  auto serverEndpoint = Endpoint{argv[2]};
  auto context = Context{};
  auto socket = Socket{context, SocketType::request};
  socket.connect(serverEndpoint);
  auto state = State{};
  state.packs = readPacks(initialPackFilePath, state.packs);
  for (auto const& pack : state.packs) {
    state.knownIds.insert(pack.id);
  }
  while (true) {
    sendListRequest(socket, state);
    receiveListReply(socket, state);
    auto isRequestSent = sendGetRequest(socket, state);
    if (isRequestSent) receiveGetReply(socket, state);
    std::this_thread::sleep_for(sleep_time());
  }
  return EXIT_SUCCESS;
}
