#lang forge

option solver MiniSatProver
option logtranslation 1
option coregranularity 1
option core_minimization rce

abstract sig PitchClass {
    next: one PitchClass
}
one sig A extends PitchClass {}
one sig E extends PitchClass {}
one sig B extends PitchClass {}
one sig Fsharp extends PitchClass {}
one sig Csharp extends PitchClass {}
one sig Gsharp extends PitchClass {}
one sig Eflat extends PitchClass {}
one sig Bflat extends PitchClass {}
one sig F extends PitchClass {}
one sig C extends PitchClass {}
one sig G extends PitchClass {}
one sig D extends PitchClass {}

pred circleOfFifths { -- circle of fifths!
    next = A->E + E->B + B->Fsharp + Fsharp->Csharp + Csharp->Gsharp + Gsharp->Eflat + Eflat->Bflat + Bflat->F + F->C + C->G + G->D + D->A
}

one sig Scale {
    notes: set PitchClass,
    header: one PitchClass
}

pred pentScale {
    #notes = 5
    #((notes.next) & notes) = 4 -- consecutive 5 notes
    Scale.header = Scale.notes - (Scale.notes).next -- takes the head of the scale
}

abstract sig Note {
    pclass: one PitchClass,
    octave: one Int,
    nextnotes: lone Note, -- chain of notes
    noteLength: one Int,
    noteLengthTotal: one Int, -- accumulator for measure purposes
    var1: one Int 
}

sig NoteRight extends Note {}
sig NoteLeft extends Note {}


pred wellFormed {
    Note.pclass = Scale.notes -- want only and all notes in the scale
    (NoteRight->NoteRight + NoteLeft->NoteLeft) in *(nextnotes + ~nextnotes) -- connected next chain
    one NoteRight - NoteRight.nextnotes -- ensures one start in Right next chain
    one NoteRight - nextnotes.NoteRight -- ensures one end in Right next chain
    one NoteLeft - NoteLeft.nextnotes -- ensures one start in Left next chain
    one NoteLeft - nextnotes.NoteLeft -- ensures one end in Left next chain
    no nextnotes & iden -- no self loops in next chain
    no (NoteRight->NoteLeft + NoteLeft->NoteRight) & nextnotes -- no crossing chains
}

pred basicSound {
    (NoteRight - NoteRight.nextnotes).pclass = Scale.header -- makes first Right note '1'
    (NoteRight - nextnotes.NoteRight).pclass = Scale.header -- makes last Right note '1'
    nextnotes.(NoteRight - nextnotes.NoteRight).pclass = Scale.header.next -- makes second to last note '5'
    all n: Note | {
        sum[n.noteLength] > 0
        n in NoteRight implies sum[n.noteLength] < 5 -- note length control
        n in NoteLeft implies sum[n.noteLength] = 4
        sum[n.octave] > 0
        sum[n.octave] < 3 -- octave control
    }
}

pred variation {
    (NoteRight - NoteRight.nextnotes).var1 = sing[1] -- initialize first note run
    all pre, post: NoteRight | pre.nextnotes = post implies {
        // pre.pclass != post.pclass -- ULTIMATE VARIATION, DONT USE??
        (pre.pclass = post.pclass and pre.octave = post.octave) implies sum[post.var1] = add[sum[pre.var1], 1] -- same -> add
        else post.var1 = sing[1] -- diff -> new
    }
    NoteRight = var1.(sing[1]) + var1.(sing[2]) -- ensures only runs of 1 and 2 (of var1)
    
}

pred rhythmStuff {
    (NoteRight - NoteRight.nextnotes).noteLengthTotal = (NoteRight - NoteRight.nextnotes).noteLength -- initialize first note run
    (NoteLeft - NoteLeft.nextnotes).noteLengthTotal = (NoteLeft - NoteLeft.nextnotes).noteLength -- initialize first note run
    // remainder[sum[(NoteRight - nextnotes.NoteRight).noteLengthTotal], 4] = 0 -- makes it end on 0 mod 4
    all pre, post: Note | pre.nextnotes = post implies {
        // add[sum[pre.noteLengthTotal], sum[post.noteLength]] = 4 implies post.noteLengthTotal = sing[0]
        // else 
        post.noteLengthTotal = sing[add[sum[pre.noteLengthTotal], sum[post.noteLength]]]
    }
    all i: Int | {
        (remainder[sum[i], 4] = 0) and (sum[i] <= max[NoteRight.noteLengthTotal] and sum[i] > 0) implies (i in NoteRight.noteLengthTotal)
    }
    max[NoteRight.noteLengthTotal] = max[NoteLeft.noteLengthTotal]
}
    // max(noteLengthTotal) == 0 mod 4
    // int - (1 2 3) ==> (3 6 9)
    // sig allthefours:
    // set ints
    // allthefours: #items == noteLengthTotal/4
    // all items in allthefours == 0 mod 4  and  < noteLengthTotal/4
    // every add => 
    // (sing[0] + sing[4] + ... ) in Note.noteLengthTotal
    // all I: int st i % 4 == 0 and i< notelength run : i in note

pred soundsNotAwful {
    circleOfFifths
    pentScale
    wellFormed
    basicSound
    variation
    rhythmStuff
}

run {
    soundsNotAwful
} for exactly 12 PitchClass, exactly 16 Note, 7 Int