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

sig Note {
    pclass: one PitchClass,
    octave: one Int,
    nextnotes: lone Note, -- chain of notes
    noteLength: one Int,
    noteLengthRun: one Int, -- accumulator for measure purposes
    var1: one Int 
}

pred wellFormed {
    Note.pclass = Scale.notes -- want only and all notes in the scale
    Note->Note in *(nextnotes + ~nextnotes) -- connected next chain
    one Note - Note.nextnotes -- ensures one start in next chain
    one Note - nextnotes.Note -- ensures one end in next chain
    no nextnotes & iden -- no self loops in next chain
}

pred basicSound {
    (Note - Note.nextnotes).pclass = Scale.header -- makes first note '1'
    (Note - nextnotes.Note).pclass = Scale.header -- makes last note '1'
    nextnotes.(Note - nextnotes.Note).pclass = Scale.header.next -- makes second to last note '5'
    all n: Note | {
        sum[n.noteLength] > 0
        sum[n.noteLength] < 5 -- note length control
        sum[n.octave] > 0
        sum[n.octave] < 3 -- octave control
    }
}

pred variation {
    (Note - Note.nextnotes).var1 = sing[1] -- initialize first note run
    all pre, post: Note | pre.nextnotes = post implies {
        (pre.pclass = post.pclass and pre.octave = post.octave) implies sum[post.var1] = add[sum[pre.var1], 1] -- same -> add
        else post.var1 = sing[1] -- diff -> new
    }
    Note = var1.(sing[1]) + var1.(sing[2]) -- ensures only runs of 1 and 2 (of var1)
}

pred rhythmStuff {
    (Note - Note.nextnotes).noteLengthRun = (Note - Note.nextnotes).noteLength -- initialize first note run
    remainder[sum[(Note - nextnotes.Note).noteLengthRun], 4] = 0 -- makes it end on 0 mod 4
    all pre, post: Note | pre.nextnotes = post implies {
        add[sum[pre.noteLengthRun], sum[post.noteLength]] = 4 implies post.noteLengthRun = sing[0]
        else post.noteLengthRun = sing[add[sum[pre.noteLengthRun], sum[post.noteLength]]]
    }
}

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
} for exactly 12 PitchClass, exactly 12 Note, 7 Int