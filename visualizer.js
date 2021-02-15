//console.log("a")
console.log('\n')

const mynotes = Note.atoms()
const notenames = mynotes.map(n => n.join(octave))


//console.log(pclass.tuples().map(n => n.atoms()))
//console.log(Note.atoms()[9].join(nextnotes).tuples()[0].atoms()[0].id())
//console.log(Note.atoms()[1].join(nextnotes).tuples().map(n => n.atoms()[0].id()))

nexts = Note.join(nextnotes).tuples().map(n => n.atoms()[0])
starter = Note.atoms().filter(x => !nexts.includes(x))[0]

ordered = [starter]
for (i = 1; i != Note.atoms().length; ++i ) {
  ordered.push(ordered[i-1].join(nextnotes).tuples()[0].atoms()[0])
}

noteInfo = ordered.map(n => [n.join(pclass).tuples()[0].atoms()[0].id(), 
                             n.join(octave).tuples()[0].atoms()[0].id(),
                            n.join(noteLength).tuples()[0].atoms()[0].id()])
/*
for (i = 0; i != ordered.length(); ++i) {
  noteInfo[i] = ordered
}*/

//console.log(Note.atoms().filter(x => x.id() == "Note0"))
//console.log(starter.id())
console.log(noteInfo)
                    
//console.log(starter.join(nextnotes).tuples()[0].atoms()[0])
