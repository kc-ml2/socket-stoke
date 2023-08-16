import socket
import struct
import random
def start_server():
    server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    host = '127.0.0.1'  # Change this to your server IP if needed
    port = 12341       # Choose any available port number
    server_socket.bind((host, port))
    server_socket.listen(1)
    print("Server listening on {}:{}".format(host, port))
    while True:
        conn, addr = server_socket.accept()
        #print("Connected to", addr)
        while True:
            '''
            data = conn.recv(4)  # Receive 4 bytes (size of int)
            if len(data) != 4:
                break
            received_data = struct.unpack('i', data)[0]  # Unpack received binary data to an integer
            print("Received integer from client:", received_data)
            '''
            #num = int(input("server : "))
            num = random.randint(0,100)


            conn.sendall(struct.pack('i', num))
            
            length_buffer = conn.recv(4)
            cpu_state_length = int.from_bytes(length_buffer, byteorder='little')  # Convert bytes to integer
            cpu_state = conn.recv(cpu_state_length).decode()
            ##print("cpu_state : ",cpu_state)
            cost_buffer = conn.recv(4)
            cost = int.from_bytes(cost_buffer, byteorder='little')  # Convert bytes to integer
            
            length_buffer = conn.recv(4)
            assembly_length = int.from_bytes(length_buffer, byteorder='little')  # Convert bytes to integer
            assembly = conn.recv(assembly_length).decode()
            ##print(assembly)
            # Process the received data
            '''
            if not data:
                continue  # Connection closed by the client
            '''

            
            
        print("Connection closed with", addr)
        conn.close()
if __name__ == "__main__":
    start_server()