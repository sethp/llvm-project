//===--- InterpStack.cpp - Stack implementation for the VM ------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "InterpStack.h"
#include "Boolean.h"
#include "Floating.h"
#include "Integral.h"
#include "Interp/PrimType.h"
#include "Pointer.h"
#include "llvm/Support/Compiler.h"
#include <cassert>
#include <cstdlib>

using namespace clang;
using namespace clang::interp;

InterpStack::~InterpStack() {
  clear();
}

void InterpStack::clear() {
  if (Chunk && Chunk->Next)
    std::free(Chunk->Next);
  if (Chunk)
    std::free(Chunk);
  Chunk = nullptr;
  StackSize = 0;
#ifndef NDEBUG
  ItemTypes.clear();
#endif
}

void *InterpStack::grow(size_t Size) {
  assert(Size < ChunkSize - sizeof(StackChunk) && "Object too large");

  if (!Chunk || sizeof(StackChunk) + Chunk->size() + Size > ChunkSize) {
    if (Chunk && Chunk->Next) {
      Chunk = Chunk->Next;
    } else {
      StackChunk *Next = new (std::malloc(ChunkSize)) StackChunk(Chunk);
      if (Chunk)
        Chunk->Next = Next;
      Chunk = Next;
    }
  }

  auto *Object = reinterpret_cast<void *>(Chunk->End);
  Chunk->End += Size;
  StackSize += Size;
  return Object;
}

void *InterpStack::peekData(size_t Size) const {
  assert(Chunk && "Stack is empty!");

  StackChunk *Ptr = Chunk;
  while (Size > Ptr->size()) {
    Size -= Ptr->size();
    Ptr = Ptr->Prev;
    assert(Ptr && "Offset too large");
  }

  return reinterpret_cast<void *>(Ptr->End - Size);
}

void InterpStack::shrink(size_t Size) {
  assert(Chunk && "Chunk is empty!");

  while (Size > Chunk->size()) {
    Size -= Chunk->size();
    if (Chunk->Next) {
      std::free(Chunk->Next);
      Chunk->Next = nullptr;
    }
    Chunk->End = Chunk->start();
    Chunk = Chunk->Prev;
    assert(Chunk && "Offset too large");
  }

  Chunk->End -= Size;
  StackSize -= Size;
}

LLVM_DUMP_METHOD void InterpStack::dump() const {
#ifndef NDEBUG
  llvm::errs() << "Items: " << ItemTypes.size() << ". Size: " << size() << '\n';
  if (ItemTypes.empty())
    return;

  size_t Index = 0;
  size_t Offset = 0;

  // The type of the item on the top of the stack is inserted to the back
  // of the vector, so the iteration has to happen backwards.
  for (auto TyIt = ItemTypes.rbegin(); TyIt != ItemTypes.rend(); ++TyIt) {
    Offset += align(primSize(*TyIt));

    llvm::errs() << Index << '/' << Offset << ": ";
    TYPE_SWITCH(*TyIt, {
      const T &V = peek<T>(Offset);
      llvm::errs() << V;
    });
    if (*TyIt == PT_Ptr) {
      if (peek<Pointer>(Offset).isZero())
        llvm::errs() << "\tnullptr\n";
      else
        llvm::errs() << "\t*(" << peek<Pointer>(Offset).getType() << ")\n";
      continue;
    }

    llvm::errs() << "\t<";
    switch (*TyIt) {
    case PT_Sint8: {
      llvm::errs() << "PT_Sint8";
      break;
    }
    case PT_Uint8: {
      llvm::errs() << "PT_Uint8";
      break;
    }
    case PT_Sint16: {
      llvm::errs() << "PT_Sint16";
      break;
    }
    case PT_Uint16: {
      llvm::errs() << "PT_Uint16";
      break;
    }
    case PT_Sint32: {
      llvm::errs() << "PT_Sint32";
      break;
    }
    case PT_Uint32: {
      llvm::errs() << "PT_Uint32";
      break;
    }
    case PT_Sint64: {
      llvm::errs() << "PT_Sint64";
      break;
    }
    case PT_Uint64: {
      llvm::errs() << "PT_Uint64";
      break;
    }
    case PT_IntAP: {
      llvm::errs() << "PT_IntAP";
      break;
    }
    case PT_IntAPS: {
      llvm::errs() << "PT_IntAPS";
      break;
    }
    case PT_Float: {
      llvm::errs() << "PT_Float";
      break;
    }
    case PT_Bool: {
      llvm::errs() << "PT_Bool";
      break;
    }
    case PT_Ptr: {
      llvm::errs() << "PT_Ptr";
      break;
    }
    case PT_FnPtr: {
      llvm::errs() << "PT_FnPtr";
      break;
    }
    }
    llvm::errs() << ">\n";

    ++Index;
  }
#endif
}

#ifndef NDEBUG
const Pointer &InterpStack::peekPtr(size_t Skips) const {
  assert(ItemTypes.size() > Skips);
  size_t Offset = align(primSize(PT_Ptr));
  auto I = ItemTypes.rbegin(), E = ItemTypes.rend();
  for (; Skips > 0 && I != E; ++I, --Skips)
    Offset += align(primSize(*I));
  assert(I < E && *I == PT_Ptr);
  return peek<Pointer>(Offset);
}
#endif
