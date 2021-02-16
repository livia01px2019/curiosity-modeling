//console.log("a")


//const mynotes = Note.atoms()
//const notenames = mynotes.map(n => n.join(octave))


//console.log(pclass.tuples().map(n => n.atoms()))
//console.log(Note.atoms()[9].join(nextnotes).tuples()[0].atoms()[0].id())
//console.log(Note.atoms()[1].join(nextnotes).tuples().map(n => n.atoms()[0].id()))

/*
for (i = 0; i != ordered.length(); ++i) {
  noteInfo[i] = ordered
}*/

//console.log(Note.atoms().filter(x => x.id() == "Note0"))
//console.log(starter.id())
//console.log(noteInfo)
                    
//console.log(starter.join(nextnotes).tuples()[0].atoms()[0])


// -----------------------------------------------------------
// Debugging above, functionality below
// -----------------------------------------------------------

console.log('\n')

// weird forge shit to find notes
nexts = Note.join(nextnotes).tuples().map(n => n.atoms()[0])
starter = Note.atoms().filter(x => !nexts.includes(x))[0]

ordered = [starter];
for (i = 1; i != Note.atoms().length; ++i ) {
  ordered.push(ordered[i-1].join(nextnotes).tuples()[0].atoms()[0]);
};

noteInfo = ordered.map(n => [n.join(pclass).tuples()[0].atoms()[0].id(), 
  n.join(octave).tuples()[0].atoms()[0].id(), n.join(noteLength).tuples()[0].atoms()[0].id()]);

// here lies ~music~ kinda
const pitches = {C: 261.63, Csharp: 277.18, D: 293.66, Eflat: 311.13, E: 329.63, F: 349.23, 
  Fsharp: 369.99, G: 392.00, Gsharp: 415.30, A: 440.00, Bflat: 466.16, B: 493.88}; // pitch dictionary

var ourContext = new AudioContext(); // must initialize 1 universal context for audio nodes
const lengthModifier = 0.5; // converts length to seconds

function playTone(freq, startTime, endTime) {
  tempOscillator = ourContext.createOscillator(); // need a new oscillator every time
  tempOscillator.frequency.value = freq; // set the frequency of the oscillator
  tempOscillator.connect(ourContext.destination); // must connect oscillator to our ears
  tempOscillator.start(startTime); // start time
  tempOscillator.stop(endTime); // end time determined when run, should be careful with choice
}

function playTheNotes(noteScore) {
  currAccTime = 0; // useful for choosing start/end times
  startedTime = ourContext.currentTime; // initialize start time
  console.log(noteScore); // debugging & gives info on score
  for (i = 0; i != noteScore.length; ++i) {
    let n = noteScore[i]; // n is a particular note array
    let currPitch = n[0].substring(0, n[0].length - 1); // removes the pesky trailing "0" from "C0", for example
    let octave = parseInt(n[1]); // octave
    let freq = pitches[currPitch] * (2 ** (octave - 1)); // every octave higher doubles the frequency
    let currLength = parseInt(n[2]) * lengthModifier; // convert note length to seconds
    playTone(freq, startedTime + currAccTime, startedTime + currAccTime + currLength); // careful tone playing
    currAccTime += currLength; // update accumulated time for timing purposes
  }
}

playTheNotes(noteInfo); // finally play everything!