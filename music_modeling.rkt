#lang forge

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
    next = A->E + E->B + B->Fsharp + Fsharp->Csharp + Csharp->Gsharp + 
            Gsharp->Eflat + Eflat->Bflat + Bflat->F + F->C + C->G + G->D + D->A
}

inst correctCircleOfFifths {
    A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0

    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->D0 + D0->A0
}

inst missingPitchClass {
    A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0

    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->A0
}

test expect {
    correctCircleOfFifthsTest: {
        circleOfFifths
    } for exactly 12 PitchClass, 7 Int for correctCircleOfFifths is sat

    missingPitchClassTest: {
        circleOfFifths
    } for exactly 12 PitchClass, 7 Int for missingPitchClass is unsat
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

inst correctPentScale {
    A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0

    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->D0 + D0->A0

    Scale = Scale0

    notes = Scale0->(A0 + E0 + B0 + Fsharp0 + Csharp0)
    header = Scale0->A0
}

inst notConsecutiveScale {
    A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0

    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->D0 + D0->A0

    Scale = Scale0

    notes = Scale0->(A0 + E0 + B0 + Fsharp0 + Gsharp)
    header = Scale0->A0
}

inst notCorrectHeader {
    A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0

    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->D0 + D0->A0

    Scale = Scale0

    notes = Scale0->(A0 + E0 + B0 + Fsharp0 + Csharp0)
    header = Scale0->Csharp0
}

test expect {
    correctPentScaleTest: {
        pentScale
    } for exactly 12 PitchClass, 7 Int for correctPentScale is sat

    notConsecutiveScaleTest: {
        pentScale
    } for exactly 12 PitchClass, 7 Int for notConsecutiveScale is unsat

    notCorrectHeaderTest: {
        pentScale
    } for exactly 12 PitchClass, 7 Int for notCorrectHeader is unsat
}

sig Note {
    pclass: one PitchClass,
    accompanyP: one PitchClass,
    octave: one Int,
    accompanyO: one Int,
    nextnotes: lone Note, -- chain of notes
    noteLength: one Int,
    noteLengthRun: one Int -- accumulator for measure purposes
}

sig NoteRight extends Note {}
sig NoteLeft extends Note {}


pred wellFormed {
    Note.pclass = Scale.notes -- want only and all notes in the scale
    Note.accompanyP in Scale.notes -- accompaniment should be in key
    Note->Note in *(nextnotes + ~nextnotes) -- connected next chain
    one Note - Note.nextnotes -- ensures one start in next chain
    one Note - nextnotes.Note -- ensures one end in next chain
    no nextnotes & iden -- no self loops in next chain
    no (NoteRight->NoteLeft + NoteLeft->NoteRight) & nextnotes -- no crossing chains
}

inst correctWellFormed {
    A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0

    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->D0 + D0->A0

    Scale = Scale0

    notes = Scale0->(A0 + E0 + B0 + Fsharp0 + Csharp0)
    header = Scale0->A0

    Note = Note0 + Note1 + Note2 + Note3 + Note4
    nextnotes = Note0->Note1 + Note1->Note2 + Note2->Note3 + Note3->Note4
    pclass = Note0->A0 + Note1->E0 + Note2->B0 + Note3->Fsharp0 + 
            Note4->Csharp0
    accompanyP = (Note0 + Note1 + Note2 + Note3 + Note4)->A0
}

inst cycleNotes {
    A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0

    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->D0 + D0->A0

    Scale = Scale0

    notes = Scale0->(A0 + E0 + B0 + Fsharp0 + Csharp0)
    header = Scale0->A0

    Note = Note0 + Note1 + Note2 + Note3 + Note4
    nextnotes = Note0->Note1 + Note1->Note2 + Note2->Note3 + Note3->Note4
                + Note4->Note0
    pclass = Note0->A0 + Note1->E0 + Note2->B0 + Note3->Fsharp0 + 
            Note4->Csharp0
    accompanyP = (Note0 + Note1 + Note2 + Note3 + Note4)->A0
}

test expect {
    correctWellFormedTest: {
        wellFormed
    } for exactly 12 PitchClass, 7 Int for correctWellFormed is sat

    cycleNotesTest: {
        wellFormed
    } for exactly 12 PitchClass, 7 Int for cycleNotes is unsat
}

pred basicSound {
    (NoteRight - NoteRight.nextnotes).pclass = Scale.header -- makes first Right note '1'
    (NoteRight - nextnotes.NoteRight).pclass = Scale.header -- makes last Right note '1'
    nextnotes.(NoteRight - nextnotes.NoteRight).pclass = Scale.header.next -- makes second to last note '5'
    all n: Note | {
        sum[n.noteLength] > 0
        sum[n.noteLength] < 3 -- note length control
        sum[n.octave] > 0
        sum[n.octave] < 3 -- octave control

        sum[n.accompanyO] = subtract[sum[n.octave], 1] -- accompaniment is lower
        (n.pclass != n.accompanyP.next.next) and (n.accompanyP != n.pclass.next.next) 
        -- accompaniment is not 2 hops away from main (sounds dissonant)
    }
}

inst correctBasicSound {
    A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0

    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->D0 + D0->A0

    Scale = Scale0

    notes = Scale0->(A0 + E0 + B0 + Fsharp0 + Csharp0)
    header = Scale0->A0

    Note = Note0 + Note1 + Note2
    nextnotes = Note0->Note1 + Note1->Note2

    pclass = Note0->A0 + Note1->E0 + Note2->A0
    octave = Note0->1 + Note1->1 + Note2->2
    accompanyP = Note0->A0 + Note1->B0 + Note2->Fsharp0
    accompanyO = Note0->0 + Note1->0 + Note2->1

    noteLength = Note0->sing[1] + Note1->sing[1] + Note2->sing[2]
}

inst dissonantAccompaniment {
    A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0

    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->D0 + D0->A0

    Scale = Scale0

    notes = Scale0->(A0 + E0 + B0 + Fsharp0 + Csharp0)
    header = Scale0->A0

    Note = Note0 + Note1 + Note2
    nextnotes = Note0->Note1 + Note1->Note2

    pclass = Note0->A0 + Note1->E0 + Note2->A0
    octave = Note0->1 + Note1->1 + Note2->2
    accompanyP = Note0->B0 + Note1->B0 + Note2->Fsharp0
    accompanyO = Note0->0 + Note1->0 + Note2->1

    noteLength = Note0->sing[1] + Note1->sing[1] + Note2->sing[2]
}

test expect {
    correctBasicSoundTest: {
        basicSound
    } for exactly 12 PitchClass, 7 Int for correctBasicSound is sat

    dissonantAccompanimentTest: {
        basicSound
    } for exactly 12 PitchClass, 7 Int for dissonantAccompaniment is unsat
}

pred noteVariation {
    all pre, post: Note | pre.nextnotes = post implies {
        not (pre.pclass = post.pclass and pre.octave = post.octave) -- no doubling main
        not (pre.accompanyP = post.accompanyP and pre.accompanyO = post.accompanyO) 
        -- no doubling accompaniment
    }
}

test expect {
    someVariation: noteVariation for exactly 12 PitchClass, 7 Int for {A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0
    PitchClass = A0+E0+B0+Fsharp0+Csharp0+Gsharp0+Eflat0+Bflat0+F0+C0+G0+D0
    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->D0 + D0->A0
    Scale = Scale0
    notes = Scale0->(A0 + E0 + B0 + Fsharp0 + Csharp0)
    header = Scale0->A0
    Note = Note1+Note2+Note3+Note4
    nextnotes = Note1->Note2 + Note2->Note3 + Note3->Note4
    pclass = Note1->A0 + Note2->A0 + Note3->Fsharp0 + Note4->Csharp0
    accompanyP = Note1->E0 + Note2->Fsharp0 + Note3->Csharp0 + Note4->Fsharp0
    octave = Note1->sing[1] + Note2->sing[2] + Note3->sing[1] + Note4->sing[1]
    accompanyO = Note1->sing[0] + Note2->sing[0] + Note3->sing[0] + Note4->sing[0]
    noteLength = Note1->sing[1] + Note2->sing[2] + Note3->sing[1] + Note4->sing[2]} is sat
}

test expect {
    doublingNotes: noteVariation for exactly 12 PitchClass, 7 Int for {A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0
    PitchClass = A0+E0+B0+Fsharp0+Csharp0+Gsharp0+Eflat0+Bflat0+F0+C0+G0+D0
    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->D0 + D0->A0
    Scale = Scale0
    notes = Scale0->(A0 + E0 + B0 + Fsharp0 + Csharp0)
    header = Scale0->A0
    Note = Note1+Note2+Note3+Note4
    nextnotes = Note1->Note2 + Note2->Note3 + Note3->Note4
    pclass = Note1->A0 + Note2->B0 + Note3->Fsharp0 + Note4->Fsharp0
    accompanyP = Note1->E0 + Note2->Fsharp0 + Note3->Csharp0 + Note4->Fsharp0
    octave = Note1->sing[1] + Note2->sing[1] + Note3->sing[1] + Note4->sing[1]
    accompanyO = Note1->sing[1] + Note2->sing[1] + Note3->sing[1] + Note4->sing[1]
    noteLength = Note1->sing[2] + Note2->sing[1] + Note3->sing[1] + Note4->sing[2]} is unsat
}

pred rhythm {
    (Note - Note.nextnotes).noteLengthRun = (Note - Note.nextnotes).noteLength -- initialize first note run
    remainder[sum[(Note - nextnotes.Note).noteLengthRun], 4] = 0 -- makes it end on 0 mod 4
    all pre, post: Note | pre.nextnotes = post implies {
        add[sum[pre.noteLengthRun], sum[post.noteLength]] = 4 implies post.noteLengthRun = sing[0] 
        -- reset noteLengthRun back to 0 when 4 is reached, ensuring notes are divided into measures
        else post.noteLengthRun = sing[add[sum[pre.noteLengthRun], sum[post.noteLength]]]
    }
    sum[(Note - nextnotes.Note).noteLength] > 1 -- make the last note longer
}

test expect {
    rhythmOK: rhythm for exactly 12 PitchClass, 7 Int for {A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0
    PitchClass = A0+E0+B0+Fsharp0+Csharp0+Gsharp0+Eflat0+Bflat0+F0+C0+G0+D0
    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->D0 + D0->A0
    Scale = Scale0
    notes = Scale0->(A0 + E0 + B0 + Fsharp0 + Csharp0)
    header = Scale0->A0
    Note = Note1+Note2+Note3+Note4
    nextnotes = Note1->Note2 + Note2->Note3 + Note3->Note4
    pclass = Note1->A0 + Note2->A0 + Note3->Fsharp0 + Note4->Csharp0
    accompanyP = Note1->E0 + Note2->Fsharp0 + Note3->Csharp0 + Note4->Fsharp0
    octave = Note1->sing[1] + Note2->sing[2] + Note3->sing[1] + Note4->sing[1]
    accompanyO = Note1->sing[0] + Note2->sing[0] + Note3->sing[0] + Note4->sing[0]
    noteLength = Note1->sing[2] + Note2->sing[2] + Note3->sing[2] + Note4->sing[2]
    noteLengthRun = Note1->sing[2] + Note2->sing[0] + Note3->sing[2] + Note4->sing[0]} is sat
}

test expect {
    evenButNotMeasured: rhythm for exactly 12 PitchClass, 7 Int for {A = A0
    E = E0
    B = B0
    Fsharp = Fsharp0
    Csharp = Csharp0
    Gsharp = Gsharp0
    Eflat = Eflat0
    Bflat = Bflat0
    F = F0
    C = C0
    G = G0
    D = D0
    PitchClass = A0+E0+B0+Fsharp0+Csharp0+Gsharp0+Eflat0+Bflat0+F0+C0+G0+D0
    next = A0->E0 + E0->B0 + B0->Fsharp0 + Fsharp0->Csharp0 + 
            Csharp0->Gsharp0 + Gsharp0->Eflat0 + Eflat0->Bflat0 + 
            Bflat0->F0 + F0->C0 + C->G0 + G0->D0 + D0->A0
    Scale = Scale0
    notes = Scale0->(A0 + E0 + B0 + Fsharp0 + Csharp0)
    header = Scale0->A0
    Note = Note1+Note2+Note3+Note4
    nextnotes = Note1->Note2 + Note2->Note3 + Note3->Note4
    pclass = Note1->A0 + Note2->A0 + Note3->Fsharp0 + Note4->Csharp0
    accompanyP = Note1->E0 + Note2->Fsharp0 + Note3->Csharp0 + Note4->Fsharp0
    octave = Note1->sing[1] + Note2->sing[2] + Note3->sing[1] + Note4->sing[1]
    accompanyO = Note1->sing[0] + Note2->sing[0] + Note3->sing[0] + Note4->sing[0]
    noteLength = Note1->sing[2] + Note2->sing[1] + Note3->sing[2] + Note4->sing[1]
    noteLengthRun = Note1->sing[2] + Note2->sing[3] + Note3->sing[5] + Note4->sing[6]} is unsat
}

pred soundsNotAwful {
    circleOfFifths
    pentScale
    wellFormed
    basicSound
    noteVariation
    rhythm
}

run {
    soundsNotAwful
} for exactly 12 PitchClass, exactly 16 Note, 7 Int