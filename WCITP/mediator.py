# -*- coding: utf-8 -*-
"""
Spyder Editor

This is a temporary script file.
"""

from subprocess import Popen, PIPE, STDOUT

from websocket_server import WebsocketServer

# Called for every client connecting (after handshake)
def new_client(client, server):
    add = client['address'][0]
    if not (add in maude_dict):
        path = '/Applications/maude-darwin/maude.darwin64'
        maude = Popen(path, stdout=PIPE, stdin=PIPE, stderr=STDOUT)
        maude.stdin.write(b"load /Users/adrian/Documents/Maude/webCITP/citp.maude\n")
        maude.stdin.flush()
        maude_dict[add] = maude
        print("New client")

# Called for every client disconnecting
def client_left(client, server):
    print("Closed")

def get_output(maude):
    end = False
    copy = False
    result = ""
    outs = maude.stdout
    while (not end):
        out = outs.readline().decode("utf-8")
        starts = out.startswith("$#") or out.startswith("Maude> $#")
        end = out.endswith("#$\n")
        if end:
            out = out[:-3]
        if copy:
            result = result + out
        if starts:
            copy = True
    return result
            

def send_output(client, server, maude):
    goals = "(show goals)\n"
    goals_bytes = bytes(goals, "utf-8")
    maude.stdin.write(goals_bytes)
    maude.stdin.flush()
    goal_out = get_output(maude).replace("\"", "\\\"")
    proof = "(show proof)\n"
    proof_bytes = bytes(proof, "utf-8")
    maude.stdin.write(proof_bytes)
    maude.stdin.flush()
    proof_out = get_output(maude).replace("\"", "\\\"")
    msg = "{ \"goal\" : \"" + goal_out + "\", \"proof\" : \"" + proof_out + "\"}\n\n"
    msg.replace("\n", "\r\n")
    msg.replace("\m", "")
    msg.replace("\o", "")
    print(msg)
    server.send_message(client, msg)

# Called when a client sends a message
def message_received(client, server, msg):
    msg.replace("\r\n", "\n")
    add = client['address'][0]
    maude = maude_dict[add]
    if (msg.startswith("Module")):
        msg = msg[6:] + "\n"
        msg_bytes = bytes(msg, "utf-8")
        maude.stdin.write(msg_bytes)
        maude.stdin.flush()
        loop = "select #CITP# .\nloop init .\n"
        loop_bytes = bytes(loop, "utf-8")
        maude.stdin.write(loop_bytes)
        maude.stdin.flush()
        print("Module introduced")
#        server.send_message(client, "{ \"goal\" : \"myGoal\", \"proof\" : \"myProof\" }")
    else:
        msg_bytes = bytes(msg, "utf-8")
        maude.stdin.write(msg_bytes)
        maude.stdin.flush()
        send_output(client, server, maude)

maude_dict = {}


PORT = 5678
server = WebsocketServer(PORT)
server.set_fn_new_client(new_client)
server.set_fn_client_left(client_left)
server.set_fn_message_received(message_received)
server.run_forever()